# VeriDNS

An end-to-end DNS resolver server written and verified in Lean 4 by Claude! Verified to what spec? To the RFC itself! Check it out here: https://basisresearch.github.io/VeriDNS/

Each module embeds the relevant passage with the `include_rfc` macro, which checks the quoted text against the original document at compile time. 

An NLP pipeline (tokeniser, part-of-speech tagger, phrase chunker,
clause parser) then reads the embedded prose and elaborates formal
`Prop` definitions from its grammatical structure. The implementation
is proven against the generated propositions, so the chain from the
words of the RFC to the theorem about the running code is
machine-checked end to end.

As an example, consider RFC 1035 §3.1 on comparing domain names:

```
Name servers and resolvers must compare labels in a case-insensitive
manner (i.e., A=a), assuming ASCII with zero parity.  Non-alphabetic
codes must match exactly.
```

From the parse of this passage the generator produces three
propositions. The manner-PP frame ("compare ... in a case-insensitive
manner") yields an invariance law over an abstract case fold. The
parenthesised `A=a` example pins the comparison at byte level, with
the numeric codes sanctioned by "assuming ASCII" in the same
sentence. The exactness sentence forbids the fold from conflating
anything outside the alphabetic range.

```lean
def namespace_compare_caseinsensitive (α : Type)
    (compare : α → α → Bool) (foldCase : α → α) : Prop :=
  ∀ (a b : α), foldCase a = foldCase b → compare a b = true

def namespace_compare_example (compare : UInt8 → UInt8 → Bool) : Prop :=
  compare 65 97 = true

def namespace_nonalphabetic_match_exactly (compare : UInt8 → UInt8 → Bool)
    (alphabetic : UInt8 → Bool) : Prop :=
  ∀ (a b : UInt8), alphabetic a = false → alphabetic b = false →
    compare a b = (a == b)
```

The implementation's name comparison is proven against all three, and
a further theorem shows every cache lookup is invariant under the case
of the queried name. Querying `EXAMPLE.COM` hits the entry stored for
`example.com`, and the proof of that fact traces back to the sentence
above.

## What is proven

The resolver is a recursive UDP server, and the properties below are
proven about its core implementation, each instantiating a spec
generated via symbolic NLP on the RFC prose.

- **Semantic correctness against the name tree.** RFC 1034 §3.1's "The
  domain name space is a tree structure" generates a recursive node
  model (labels ≤ 63 octets, distinct brother labels, the null root
  label, names as label paths), and §4.3.2's match-down algorithm
  generates the lookup obligations: whole-QNAME match → exactly the
  records of the queried type, CNAME at the node → restart at the
  canonical name, missing label → authoritative name error. A
  denotational `treeLookup` is proven against all of them — NXDOMAIN is
  the verdict *exactly* for missing nodes, and case-insensitively so
  (`EXAMPLE.COM` and `example.com` reach the same node, exist together,
  and are absent together). On top of it, semantic non-poisoning: under
  the honesty oracle (only *accepted* responses need be consistent with
  the tree — RFC 5452 matching keeps everything else out), the cache is
  a sound partial view of the tree and the resolver can only ever tell
  the client what the tree actually holds, through every cache hit,
  CNAME chase, and delegation.
- **Wire safety.** `decodeName` has machine-checked bounds on
  arbitrary input bytes; compression-pointer loops
  terminate. Malformed packets produce FORMERR, never a crash (RFC
  1035 §3.1, §4.1.4).
- **Poisoning resistance.** Responses must echo the unpredictable
  query ID and question (RFC 5452 §9.1), bogus delegations are
  rejected before they reach the cache (RFC 1034 §5.3.3), and cached
  data carries the RFC 2181 §5.4.1 credibility ranking, generated as
  an ordered enum from the section's ranked list. Forged glue provably
  can never be returned as an answer and can never evict more
  trustworthy data.
- **Cache discipline.** FIFO-bounded memory, absolute-expiry
  freshness, TTL clamping (RFC 1035 §7.3), and all-or-none RRset
  replacement (§7.4).
- **Negative caching.** Full RFC 2308 conformance, including the
  SOA-derived TTL, the one-to-three-hour cap from §5, NXDOMAIN keyed
  by ⟨QNAME, QCLASS⟩ with proven qtype-invariance, and the cached SOA
  served back in the authority section with its TTL decremented (§6).
- **Query hygiene.** FORMERR, NOTIMP, and REFUSED each instantiate
  use-condition semantics generated from the RCODE descriptions in RFC
  1035 §4.1.1.
- **Case-insensitive comparison.** As above (RFC 1035 §3.1).

Everything is additionally exercised live against the real DNS with
`dig`, since the IO loop and FFI sit outside the proof boundary.

## Building and running

```
lake build              # library + proofs
lake build veri-dns     # the server executable
.lake/build/bin/veri-dns
```

The server listens on UDP port 5300:

```
dig @127.0.0.1 -p 5300 example.com A
```

## Documentation

The literate documentation, rendered from the sources with
[Verso](https://github.com/leanprover/verso), is published at
<https://basisresearch.github.io/VeriDNS/> on every push to `main`. To
build it locally:

```
lake query :literateHtml    # output in .lake/build/literate-html/
```

When changing the metaprogramming code (`VeriDNS/RFC/`), delete
`.lake/build/literate/` and `.lake/build/literate-html/` first; the
literate cache is not invalidated by `lake build`.

## Layout

| Directory | Contents |
|---|---|
| `VeriDNS/RFC/` | The generator. `include_rfc` macro, NLP pipeline, property rule DSL. |
| `VeriDNS/Spec/` | RFC text embeddings and the specs generated from them. |
| `VeriDNS/Impl/` | Parser and serialiser, cache, resolver state machine, UDP server. |
| `VeriDNS/Proof/` | Conformance theorems connecting `Impl` to the generated specs. |
| `rfc/` | The RFC documents the embeddings are checked against. |
| `docs/architecture.md` | Design notes, per-RFC generation details. |

## Scope

VeriDNS is a recursive-only UDP resolver. TCP fallback, EDNS(0),
DNSSEC validation, DNS-over-TLS, and concurrent serving are out of
scope; truncated answers set TC=1 and are excluded from the cache per
RFC 1035 §7.4.
