export const meta = {
  name: 'veridns-mutation',
  description: 'Curated on-path mutation testing: inject observable bugs into VeriDNS/Impl, check whether the proofs still go through and whether the server misbehaves when run.',
  phases: [
    { title: 'Mutate' },
  ],
}

// Each mutant is processed by ONE fable agent, SERIALLY (a for-loop of awaited
// agent() calls), because every agent builds and reverts in the shared main
// repo working tree. The stable baseline binary at review/veri-dns is used by
// other (dynamic/differential) agents and must never be disturbed; mutants
// build .lake/build/bin/veri-dns and MUST revert + rebuild before finishing.

const REPO = '/home/yiyun/Experiments/VeriDNS'

// The controlled test rig (built by the env-setup agent) lives INSIDE the VM's
// network namespaces — NOT reachable from the host directly. Observation loop:
const RIG = `Controlled DNS rig (read ${REPO}/review/ENV.md for full detail):
- Resolver under test: veri-dns @203.0.113.2:5300 (in netns 'verid').
- Reference resolver: unbound @203.0.113.3:5301 (in netns 'unbound').
- Authoritative (nsd): root . / tld 'test.' / leaf 'example.test.' (203.0.113.10-12).
- Attacker/client vantage: netns 'attacker' (192.168.53.99).
- ADDRESSING (do not "fix" it): the rig is on 203.0.113.0/24 (TEST-NET-3) but the CLIENT is on 192.168.53.99. Forced by two opposing ACLs in Impl/Server.lean: doNotQueryNets (egress) refuses to QUERY 10/8+192.168/16+..., while defaultAcl (ingress) ONLY accepts clients from 127/8, 10/8, 172.16/12, 192.168/16 — an exact subset. So no one subnet can be both. A client on 203.0.113.99 is SILENTLY DROPPED (UDP timeout, TCP accept-then-EOF, empty log). The egress filter is ACTIVE; never set VERI_DNS_ALLOW_LOOPBACK_EGRESS=1. See review/HARNESS.md 2.1.
- The rig runs inside the VM; reach it only via '${REPO}/penn-testing/vm/ssh.sh <cmd>'.
- Query veri-dns:   ${REPO}/penn-testing/vm/ssh.sh 'ip netns exec attacker dig @203.0.113.2 -p 5300 <name> <type>'
- Query unbound:    ${REPO}/penn-testing/vm/ssh.sh 'ip netns exec attacker dig @203.0.113.3 -p 5301 <name> <type>'
- To load a freshly host-built mutant into the VM and restart ONLY veri-dns:  ${REPO}/review/env/restart-verid.sh  (copies .lake/build/bin/veri-dns in, restarts, prints a verifying dig).
- Poisoning/spoofing from the attacker ns: ${REPO}/review/env/spoof.py .
- Zone data to observe against is in ${REPO}/review/env/nsd/zones (e.g. example.test A = 203.0.113.100).`

// The curated set. Each targets on-path, security-relevant behavior the
// README explicitly claims is proven. `oughtToCatch` names the theorem/spec
// that SHOULD reject the mutation if the verification is load-bearing.
const MUTANTS = [
  {
    id: 'case-sensitive-compare',
    claim: 'RFC 1035 §3.1: labels compared case-insensitively (A=a).',
    target: 'VeriDNS/Impl/DomainName.lean:108 foldCaseByte (make it identity)',
    change: 'Make the case fold the IDENTITY (foldCaseByte b := b), i.e. comparison becomes case-SENSITIVE so EXAMPLE.COM no longer equals example.com.',
    observe: 'Prime example.test A in the fake zone, then `dig @<veri-dns> -p <port> EXAMPLE.TEST A`. Correct resolver answers case-insensitively; mutant should miss/diverge vs unbound.',
    oughtToCatch: 'namespace_compare_caseinsensitive / _example / _nonalphabetic_match_exactly and the cache/tree case-invariance theorems. This direction likely BREAKS an invariance proof (proof-caught) — the informative contrast with the over-collapse mutant below.',
  },
  {
    id: 'overcollapse-fold',
    claim: 'RFC 1035 §3.1: the case fold must equate ONLY upper/lower of the SAME letter (A=a), and distinguish different letters (A≠B).',
    target: 'VeriDNS/Spec/NetworkModel.lean:23 foldByte AND VeriDNS/Impl/DomainName.lean:108 foldCaseByte',
    change: 'Make the fold OVER-COLLAPSE: map every alphabetic byte to a single letter (e.g. A-Z and a-z all -> 97), while leaving non-alphabetic bytes exact and keeping foldByte 65 = foldByte 97. This keeps the generated compare props satisfiable (they only constrain compare RELATIVE to the fold) and keeps every invariance-under-fold theorem green, but makes distinct names collide.',
    observe: 'Prime example.test A = 1.1.1.1 in the fake zone. Query a DIFFERENT name that collides under the broken fold, e.g. `dig @<veri-dns> fxbmplf.test A` (folds equal to example.test). A correct resolver returns NXDOMAIN/its own record; the mutant serves example.test\'s 1.1.1.1 for the wrong name. Compare to unbound.',
    oughtToCatch: 'THE FLAGSHIP BAD-SPEC HYPOTHESIS. foldByte/foldCaseByte are TRUSTED definitions (rfc_proves only embeds RFC text; it does not prove the def equals the ASCII case fold). All downstream case theorems are invariance-UNDER-the-fold, preserved for any fold. If lake build stays GREEN under this mutation while the server collides distinct names, the case-insensitivity spec is not load-bearing — it reduces to trusting the fold definition.',
  },
  {
    id: 'constant-query-id',
    claim: 'RFC 5452: unpredictable 16-bit query ID.',
    target: 'ffi/recvfrom.c (veri_dns_random_u16)',
    change: 'Make veri_dns_random_u16 return a constant (e.g. 0x1337) instead of getrandom.',
    observe: 'Send two queries and capture outgoing packets (tcpdump on the upstream side); the query IDs are identical/predictable. This is an off-path FFI change.',
    oughtToCatch: 'NOTHING proves the FFI random source — this should demonstrate a COVERAGE GAP (unverified glue), not a bad spec. Confirms the on/off-path boundary.',
  },
  {
    id: 'disable-bailiwick',
    claim: 'RFC 1034 §5.3.3 / RFC 5452: reject out-of-bailiwick records before caching.',
    target: 'VeriDNS/Impl/Resolver.lean or the respInBailiwick filter used on responses',
    change: 'Weaken the bailiwick check so out-of-bailiwick records in a response are accepted/cached.',
    observe: 'From the attacker vantage, answer a delegation with an out-of-bailiwick glue/answer record; check whether it is served to a client or accepted into the cache.',
    oughtToCatch: 'respInBailiwick_sound and the non-poisoning soundness (ioResumeLoop_sound). If proofs stay green, the bailiwick spec is weak.',
  },
  {
    id: 'no-ttl-clamp',
    claim: 'RFC 1035 §7.3 / RFC 2308 §5: TTL clamping and negative-TTL cap.',
    target: 'VeriDNS/Impl/Cache.lean (TTL cap on insert)',
    change: 'Remove the TTL upper-bound clamp so an attacker-supplied huge TTL is stored verbatim.',
    observe: 'Serve a record with TTL 999999999; query the resolver and read the TTL it returns; compare to unbound and to the RFC cap.',
    oughtToCatch: 'TtlCap theorems / cache freshness spec.',
  },
  {
    id: 'scrub-passthrough',
    claim: 'Client-delivery answer scrub: no record whose owner is foreign to the QNAME/CNAME-chain is returned.',
    target: 'VeriDNS/Impl/AnswerScrub.lean (scrubAnswerB)',
    change: 'Make scrubAnswerB a pass-through that returns every record unchanged (no owner filtering).',
    observe: 'Have an authoritative server include an unrelated record (e.g. victim.test A 6.6.6.6) in an answer for example.test; check whether the resolver forwards/caches it.',
    oughtToCatch: 'scrubAnswerB_excludes_foreign / scrubAnswerB_authentic / scrubAnswerB_delivered_model_authentic. If green, the scrub spec is vacuous.',
  },
  {
    id: 'forward-compression-pointer',
    claim: 'RFC 1035 §4.1.4: compression pointers must point strictly backward; no loops.',
    target: 'VeriDNS/Impl/DomainName.lean or Message.lean (decodeName pointer check)',
    change: 'Remove the strictly-backward pointer check so forward/self pointers are followed.',
    observe: 'Send a crafted packet with a forward/self compression pointer; check for hang/crash/FORMERR vs correct rejection.',
    oughtToCatch: 'decodeName termination/bounds (wire-safety) theorems.',
  },
  {
    id: 'nxdomain-to-noerror',
    claim: 'RFC 1034 §4.3.2: missing label yields authoritative name error (NXDOMAIN).',
    target: 'VeriDNS/Impl/Resolver.lean (missing-node / NXDOMAIN verdict)',
    change: 'Return NOERROR/empty instead of NXDOMAIN for a genuinely missing name.',
    observe: '`dig` a name known-absent in the fake hierarchy; expect NXDOMAIN, mutant returns NOERROR. Compare to unbound.',
    oughtToCatch: 'treeLookup_nodata_sound / the NXDOMAIN-exactly-for-missing-nodes theorem.',
  },
  {
    id: 'accept-mismatched-qid',
    claim: 'RFC 5452 §9.1: responses must echo the query ID and question.',
    target: 'VeriDNS/Impl/Resolver.lean (response acceptance / 5452 matching)',
    change: 'Skip the query-ID (or question) match so responses with the wrong ID are accepted.',
    observe: 'From the attacker vantage, race a spoofed response with a wrong/guessed ID; check whether it is accepted (poisoning).',
    oughtToCatch: 'the RFC 5452 matching predicate feeding the honesty oracle in ioResumeLoop_sound.',
  },
]

phase('Mutate')
log(`Curated mutation batch: ${MUTANTS.length} on-path mutants, serial (shared build tree).`)

const VERDICT = {
  type: 'object',
  additionalProperties: false,
  required: ['id', 'applied', 'buildGreen', 'observable', 'classification', 'evidence', 'reverted'],
  properties: {
    id: { type: 'string' },
    applied: { type: 'boolean', description: 'Was the mutation successfully applied to the source?' },
    buildGreen: { type: 'boolean', description: 'Did `lake build` (all proofs) still succeed WITH the mutation in place?' },
    observable: { type: 'boolean', description: 'Did the running mutated server exhibit the wrong behavior?' },
    classification: {
      type: 'string',
      enum: ['bad-spec', 'coverage-gap', 'proof-caught', 'not-observable', 'inconclusive'],
      description: 'bad-spec = buildGreen AND observable AND an on-path theorem ought to have caught it; coverage-gap = buildGreen AND observable but no theorem covers it (unverified glue); proof-caught = build failed / proof broke (good); not-observable = build green but no wrong behavior reproduced; inconclusive = could not determine.',
    },
    evidence: { type: 'string', description: 'Concrete evidence: the build result line, and the dig/tcpdump output or lack thereof. Cite commands.' },
    findingFile: { type: 'string', description: 'Path to review/findings/NNN-*.md written for a bad-spec or coverage-gap, else empty.' },
    reverted: { type: 'boolean', description: 'Was the source reverted (git checkout) and rebuilt green before finishing?' },
  },
}

const results = []
for (let i = 0; i < MUTANTS.length; i++) {
  const m = MUTANTS[i]
  const v = await agent(
    `You are a mutation-testing agent for the VeriDNS verified DNS resolver at ${REPO}. You run SERIALLY in the shared main working tree — you MUST leave it clean.

MUTANT #${i + 1}/${MUTANTS.length}: ${m.id}
RFC claim under test: ${m.claim}
Target: ${m.target}
Mutation to inject: ${m.change}
How to observe the bug at runtime: ${m.observe}
Theorem/spec that OUGHT to reject this if verification is load-bearing: ${m.oughtToCatch}

Environment:
${RIG}

STEPS — do them in order and DO NOT SKIP the revert:
1. Read the target source to find the exact site. Apply the mutation with a minimal edit. If you genuinely cannot locate the site, set applied=false and explain.
2. From ${REPO}, run \`lake build\` and record whether it succeeds (proofs green) or fails (proof/type error rejected the mutation). This is the KEY signal. If it builds green, also \`lake build veri-dns\`.
3. If it built green, load the mutant into the VM and restart just veri-dns with \`${REPO}/review/env/restart-verid.sh\`. Reproduce the wrong behavior by querying from the attacker ns (see RIG), comparing veri-dns @203.0.113.2:5300 against unbound @203.0.113.3:5301. Capture the actual dig/tcpdump output as evidence. (For FFI/spoofing mutants use ${REPO}/review/env/spoof.py from the attacker ns.)
4. Classify per the schema: bad-spec vs coverage-gap vs proof-caught vs not-observable.
5. If bad-spec or coverage-gap (a real finding), write a report to ${REPO}/review/findings/ named NNN-mutation-${m.id}.md (pick the next free NNN, zero-padded 3 digits) documenting: the claim, the exact mutation (diff), the build result proving proofs stayed green, the reproduction commands + output, and why it is undesirable with an RFC/unbound citation.
6. MANDATORY CLEANUP: revert the source with \`git checkout -- <files>\` (and remove any stray files), then run \`lake build\` and \`${REPO}/review/env/restart-verid.sh\` to restore the green baseline binary in the VM. Set reverted=true only if git status shows the tracked source clean again and the baseline resolves normally.

Return the structured verdict.`,
    { label: `mut:${m.id}`, phase: 'Mutate', model: 'fable', schema: VERDICT }
  )
  results.push(v)
  if (v) log(`[${m.id}] build=${v.buildGreen ? 'GREEN' : 'broke'} observable=${v.observable} -> ${v.classification}`)
}

const clean = results.filter(Boolean)
const badSpecs = clean.filter(r => r.classification === 'bad-spec')
const gaps = clean.filter(r => r.classification === 'coverage-gap')
const caught = clean.filter(r => r.classification === 'proof-caught')
log(`Mutation done. bad-spec=${badSpecs.length} coverage-gap=${gaps.length} proof-caught=${caught.length}`)
return { total: clean.length, badSpecs, gaps, caught, all: clean }
