# 038 — Promiscuous NS smuggled in the ANSWER section of a positive answer is
cached at answer credibility and redirects the whole in-bailiwick subtree;
unbound strips it

- **Component:** `VeriDNS/Impl/Resolver.lean:423-429` (answer branch caches
  `bailiwickRaws(sname, resp.answer)` via `cacheUnlessTruncated` at
  `credAnswer(aa)=authoritativeSection`, **type-agnostically**) +
  `:186-190` (`cacheRRs` accepts every parsed RR, including NS type 2) +
  `walkNs` / `lookupTopCred` (`Impl/Resolver.lean:331-346`,
  `Impl/Cache.lean:140-146`).
- **Severity:** defense-in-depth divergence (missing normalization) with a
  concrete subtree-redirect impact under the spoofing/fragmentation threat
  model. Confirmed on the rig.
- **Classification:** impl-bug (over-acceptance; a scrubbing step unbound
  performs and veri-dns omits).

## Summary

The positive-answer branch of `stepAnalyzeResponse` caches every RR in the
ANSWER section whose **owner** is at or below the query name (`isAncestorB
sname owner`), with **no per-type filter** and at `credAnswer(aa=1) =
Trustworthiness.authoritativeSection`. `authoritativeSection.toCode = 2`
(`Spec/Credibility.lean:107`) — strictly more credible than a legitimately
obtained referral's NS (`authoritySection.toCode = 3`) or glue
(`additionalAuthoritative.toCode = 6`), and lower code wins in
`maxRankForKey`/`lookupTopCred`.

Therefore an authoritative answer to `www.example.test A` that carries an
extra, unsolicited `www.example.test NS evil.example.test` RRset in the ANSWER
section installs a **top-credibility delegation** for `www.example.test`.
A later query for any descendant (`host.www.example.test`) makes `walkNs`
climb to `www.example.test`, find the cached promiscuous NS, resolve
`evil.example.test`, and send the descendant query to the attacker-chosen
server — hijacking the entire `www.example.test` subtree from a single
positive answer.

unbound removes exactly this: `iter_scrub.c:723-747`
(`iter_scrub_promiscuous`: "remove 'promiscuous' NS RRset that appears in a
positive answer", guarded by `msg->an_rrsets != 0`) and the answer-section
type filter `iter_scrub.c:659-664` (`qinfo->qtype != rrset->type` → remove
irrelevant RRset).

## Rig setup

A custom authoritative-for-`example.test` responder replaces the leaf `nsd`
on `10.53.0.12:53` (`review/env/evil_responder.py`, staged into the VM). Both
resolvers are delegated to it by the still-running tld `nsd`. For
`www.example.test A` it returns the poisoned positive answer:

```
;; ANSWER    www.example.test.  A   1.2.3.4         (aa=1)
;;           www.example.test.  NS  evil.example.test.   <-- promiscuous
;; ADDITIONAL evil.example.test. A  10.53.0.99            (attacker server)
```

It also serves `evil.example.test A = 10.53.0.99` so the promiscuous NS
target resolves in-bailiwick; `10.53.0.99` is the attacker namespace, where
tcpdump watches for redirected queries.

Bring-up:

```sh
# stop the real leaf, run the evil responder in its place (auth ns, 10.53.0.12:53)
cp /root/dev/_vmdns/evil_responder.py /opt/dnsenv/evil_responder.py
systemctl stop veridns-auth-leaf
systemd-run --unit=veridns-evil --collect ip netns exec auth \
    python3 /opt/dnsenv/evil_responder.py
```

Direct dig at the responder confirms the injection:

```
;; ANSWER SECTION:
www.example.test.  300 IN A  1.2.3.4
www.example.test.  300 IN NS evil.example.test.
;; ADDITIONAL SECTION:
evil.example.test. 300 IN A  10.53.0.99
```

## Reproduction — veri-dns (redirected to attacker)

```sh
review/env/restart-verid.sh          # clear veri-dns cache

# capture at the attacker vantage (10.53.0.99)
ip netns exec attacker tcpdump -n -i v-attacker "udp and dst host 10.53.0.99" &

# STEP 1: prime -- caches the promiscuous NS
ip netns exec attacker dig +short @10.53.0.2 -p 5300 www.example.test A
#   1.2.3.4
#   evil.example.test.          <-- veri-dns KEPT the promiscuous NS in its reply

# STEP 2: follow-up on a descendant name
ip netns exec attacker dig @10.53.0.2 -p 5300 host.www.example.test A
#   ;; communications error ... timed out
```

tcpdump at the attacker:

```
IP 10.53.0.2.58809 > 10.53.0.99.53: 48300 A? host.www.example.test. (39)
IP 10.53.0.2.47420 > 10.53.0.99.53: 48300 A? host.www.example.test. (39)
IP 10.53.0.2.52649 > 10.53.0.99.53: 48300 A? host.www.example.test. (39)
```

veri-dns (`10.53.0.2`) sent the descendant query for `host.www.example.test`
straight to the attacker-chosen server `10.53.0.99` — proving the
answer-section NS was cached at authoritative credibility and preferred by
`walkNs` over the real `example.test` delegation.

## Reproduction — unbound (strips it, follows real delegation)

```sh
systemctl restart veridns-ref        # clear unbound cache

# STEP 1
ip netns exec attacker dig @10.53.0.3 -p 5301 www.example.test A
#   ;; ANSWER SECTION:
#   www.example.test.  300 IN A 1.2.3.4      <-- ONLY the A; NS stripped

# STEP 2, captured at the leaf (auth ns, v-auth, dst 10.53.0.12)
ip netns exec attacker dig @10.53.0.3 -p 5301 host.www.example.test A
```

tcpdump at the leaf `10.53.0.12`:

```
IP 10.53.0.3.39177 > 10.53.0.12.53: 31928% [1au] A? host.www.example.test. (50)
```

unbound sent the descendant query to the **legitimate** `example.test`
nameserver (`10.53.0.12`), never to `10.53.0.99`. Capturing on the attacker
vantage during the unbound run shows **zero** packets to `10.53.0.99`.

## Why it matters

The bailiwick (owner) filter constrains the promiscuous NS owner to be at/below
the query name, i.e. inside the answering server's own subtree, so in the
non-spoofed case a server truly authoritative for `example.test` is entitled to
delegate `www.example.test` — this is defense-in-depth, not a clean cross-zone
poison. The security value that unbound's scrub provides, and veri-dns lacks:

- **Single-packet subtree hijack.** Under RFC 5452, an off-path attacker who
  wins the txid/source-port gate on one positive answer installs a
  `authoritativeSection` (code 2) delegation that is strictly more credible and
  independently TTL'd than glue, redirecting the *entire* in-bailiwick subtree —
  instead of having to win the race again on every descendant query.
- **No type discipline.** The answer branch caches any RR type whose owner is
  in-bailiwick; unbound additionally drops any answer RRset whose type ≠ qtype
  (`iter_scrub.c:659-664`).

## Citations

- RFC 2181 §5.4.1 (ranking of data; answer/authoritative data outranks
  glue/additional) — `authoritativeSection.toCode=2 < authoritySection=3 <
  additionalAuthoritative=6` (`VeriDNS/Spec/Credibility.lean:107-111`).
- unbound `iterator/iter_scrub.c:723-747` `iter_scrub_promiscuous` — removes
  NS RRsets appearing in a positive (`msg->an_rrsets != 0`) answer.
- unbound `iterator/iter_scrub.c:659-664` — removes answer RRsets whose
  `rrset->type != qinfo->qtype`.

## Teardown / restore

```sh
systemctl stop veridns-evil
systemctl start veridns-auth-leaf
```
