export const meta = {
  name: 'veridns-bug-hunt',
  description: 'Integrated iterative bug hunt: each round the finders (reading-source, spec-auditor, differential/pentest) and a mutation-synthesis stage feed a serial weaponize+verify stage; verdicts + reasons accumulate in a knowledge base that drives sharper mutations next round. Loops until dry.',
  phases: [
    { title: 'Find' },
    { title: 'Synthesize' },
    { title: 'Verify' },
  ],
}

const REPO = '/home/yiyun/Experiments/VeriDNS'
const MAX_ROUNDS = 12         // raised again: round-8 run capped WITHOUT going dry, so extend to let it reach genuine exhaustion (finders dedupe vs all prior candidates, so fresh-count converges to 0)
const DRY_ROUNDS_TO_STOP = 2  // stop only after TWO consecutive rounds with no fresh candidate — a real dry signal, not a one-round lull

// Controlled rig (built + verified by the env-setup agent) lives INSIDE the VM.
const RIG = `Controlled DNS rig (full runbook: ${REPO}/review/ENV.md):
- veri-dns (under test) @203.0.113.2:5300 in netns 'verid'; unbound (reference) @203.0.113.3:5301 in netns 'unbound'.
- nsd authoritative: root . / tld 'test.' / leaf 'example.test.' (203.0.113.10-12); zones in ${REPO}/review/env/nsd/zones (example.test A=203.0.113.100, host.example.test A=203.0.113.101, www CNAME example.test).
- attacker/client vantage: netns 'attacker' 192.168.53.99 (dig, tcpdump, ${REPO}/review/env/spoof.py).
- ADDRESSING (do not "fix" it): the rig is on 203.0.113.0/24 (TEST-NET-3) but the CLIENT is on 192.168.53.99. Forced by two opposing ACLs in Impl/Server.lean: doNotQueryNets (egress) refuses to QUERY 10/8+192.168/16+..., while defaultAcl (ingress) ONLY accepts clients from 127/8, 10/8, 172.16/12, 192.168/16 — an exact subset. So no one subnet can be both. A client on 203.0.113.99 is SILENTLY DROPPED (UDP timeout, TCP accept-then-EOF, empty log). The egress filter is ACTIVE; never set VERI_DNS_ALLOW_LOOPBACK_EGRESS=1. See review/HARNESS.md 2.1.
- Rig is INSIDE the VM; reach it only via '${REPO}/penn-testing/vm/ssh.sh <cmd>'.
- Query veri-dns: ${REPO}/penn-testing/vm/ssh.sh 'ip netns exec attacker dig @203.0.113.2 -p 5300 <name> <type>'
- Query unbound: ${REPO}/penn-testing/vm/ssh.sh 'ip netns exec attacker dig @203.0.113.3 -p 5301 <name> <type>'
- Load a freshly host-built binary into the VM + restart ONLY veri-dns: ${REPO}/review/env/restart-verid.sh (then re-query).
- Spoof/poison from attacker ns: ${REPO}/review/env/spoof.py (args in ENV.md).`

// Round-1 seeds for the mutation synthesizer: on-path claims worth probing.
// Annotated with results already known from the earlier curated run so the
// synthesizer does not blindly repeat them.
const SEED_MUTANTS = `Known on-path targets (already-tried noted):
- foldCaseByte/foldByte case fold (Impl/DomainName.lean:108, Spec/NetworkModel.lean:23). IDENTITY fold => proof-caught by the real A=a example (namespace_compare_example) [done]. NAIVE over-collapse (all letters->'a') => proof-caught, but ONLY by (i) the BRITTLE script of foldCaseByte_nonalphabetic_exact (Proof/DomainName.lean:655; its 'rw [hc.1]; simp' assumes the if has just the 65-90 branch) and (ii) incidental rfl-checked concrete traces in Spec/NetworkTraces.lean — NOT by a semantic obligation. REFINE: a SURGICAL over-collapse (e.g. map just one extra letter pair, choosing letters absent from the NetworkTraces concrete names), plus a minimal repair of the brittle nonalphabetic proof script, to test whether the SPEC (not proof-script incidentals) actually forbids conflating distinct letters. If green+observable => bad-spec, strengthening finding 001.
- constant query ID (ffi/recvfrom.c veri_dns_random_u16) => build green, observable, coverage-gap [done: finding 002].
- bailiwick filter (Impl/Resolver.lean bailiwickRaws / respInBailiwick): weaken to accept out-of-bailiwick => should break respInBailiwick_sound / soundness. NOTE: a REAL behavioral divergence already exists (see KB: veri-dns accepts grandchild answered authoritatively from the root IP; unbound rejects) — prioritize confirming/exploiting that.
- TTL clamp (Impl/Cache.lean), answer scrub (Impl/AnswerScrub.lean scrubAnswerB), compression-pointer backward check (Impl/DomainName.lean / Message.lean), NXDOMAIN->NOERROR (Impl/Resolver.lean), RFC 5452 id/question acceptance (Impl/Resolver.lean acceptResponse).`

// Seed knowledge from Phase 0 + the env agent's differential observations.
const SEED_KB = [
  'CONFIRMED 000 (medium, coverage-gap): veri-dns failed to link on Linux (arc4random) in the unverified FFI carrying RFC5452 query-ID entropy.',
  'CONFIRMED 001 (high, bad-spec, being refined): generated namespace_compare_* props are one-sided; case-insensitivity reduces to the TRUSTED foldByte definition. Under-folding is caught by the A=a example; over-folding is caught only by a brittle proof script + incidental concrete traces, not a real spec obligation.',
  'CONFIRMED 002 (coverage-gap): constant query ID builds green + observable (constant txid on the wire) — FFI unverified.',
  "LEAD (differential): veri-dns ACCEPTS a grandchild name answered authoritatively from the ROOT IP; unbound rejects it as out-of-bailiwick (NXDOMAIN). Possible bailiwick-leniency / cache-poisoning vector — HIGH priority to confirm & assess exploitability.",
  "LEAD (differential): veri-dns does not special-case RFC 6761 '.test' (unbound returns built-in NXDOMAIN). Low severity / scope.",
  'HONESTY ORACLE: at M=IO NetworkConsistent is assumed not proven; real anti-poison enforcement rests on unverified FFI (id entropy + src/dst matching). Pentest the src/dst matching directly (spoofed-response race from attacker ns).',
]

// --- schemas ---------------------------------------------------------------
const CANDIDATE = {
  type: 'object', additionalProperties: false,
  required: ['title', 'kind', 'location', 'rationale', 'howToVerify', 'severity'],
  properties: {
    title: { type: 'string' },
    kind: { type: 'string', enum: ['discrepancy', 'weak-theorem', 'impl-bug', 'scope-gap'] },
    location: { type: 'string' },
    rationale: { type: 'string' },
    howToVerify: { type: 'string' },
    severity: { type: 'string', enum: ['critical', 'high', 'medium', 'low', 'info'] },
  },
}
const CANDIDATES = {
  type: 'object', additionalProperties: false, required: ['candidates', 'notes'],
  properties: { candidates: { type: 'array', items: CANDIDATE }, notes: { type: 'string' } },
}
const MUTANT = {
  type: 'object', additionalProperties: false,
  required: ['id', 'target', 'change', 'expectedObservable', 'oughtToCatch', 'distinguish'],
  properties: {
    id: { type: 'string' },
    target: { type: 'string', description: 'file:line to mutate' },
    change: { type: 'string', description: 'the exact minimal edit' },
    expectedObservable: { type: 'string', description: 'the wrong runtime behavior + how to observe it on the rig' },
    oughtToCatch: { type: 'string', description: 'which theorem/spec should reject this if verification is load-bearing' },
    distinguish: { type: 'string', description: 'how to tell a genuine semantic catch (theorem statement becomes FALSE) from proof-script brittleness (statement still true, only the tactic fails) — and whether a minimal proof-script repair is worth attempting.' },
  },
}
const MUTANTS = {
  type: 'object', additionalProperties: false, required: ['mutants', 'rationale'],
  properties: { mutants: { type: 'array', items: MUTANT }, rationale: { type: 'string' } },
}
const VERDICT = {
  type: 'object', additionalProperties: false,
  required: ['title', 'buildGreen', 'observable', 'classification', 'reason', 'evidence'],
  properties: {
    title: { type: 'string' },
    buildGreen: { type: 'boolean' },
    observable: { type: 'boolean' },
    classification: { type: 'string', enum: ['bad-spec', 'coverage-gap', 'impl-bug', 'proof-caught-semantic', 'proof-caught-brittle', 'refuted', 'inconclusive'],
      description: 'proof-caught-semantic = a theorem STATEMENT became false (verification load-bearing here); proof-caught-brittle = only a tactic broke, statement still true (weak evidence); bad-spec = green (possibly after a minimal script repair) AND observably wrong.' },
    reason: { type: 'string', description: 'ONE line for the knowledge base: what caught it (which theorem/file) or why it slipped. Drives next round.' },
    evidence: { type: 'string', description: 'commands + outputs: the build result line, the mutation diff, and the dig/tcpdump comparison vs unbound.' },
    findingFile: { type: 'string' },
  },
}

// --- state -----------------------------------------------------------------
const key = c => `${c.kind}|${c.location}|${c.title}`.toLowerCase().replace(/\s+/g, ' ').trim()
const seen = new Set()
const confirmed = []
const kb = [...SEED_KB]
const mutantLog = []            // {id, classification, reason}
const allCandidates = []
let dryRounds = 0

const kbSummary = () => `KNOWLEDGE BASE (accumulated; build on it, do not repeat settled items):
${kb.map(s => '- ' + s).join('\n')}
MUTANTS ALREADY TRIED: ${mutantLog.length ? mutantLog.map(m => `${m.id}=${m.classification}(${m.reason})`).join(' | ') : 'none yet'}`

// Resilient agent call: agent() returns null on a terminal API error (e.g. 529
// Overloaded after its own retries). A null finder must NOT be mistaken for "no
// findings" (that produced the earlier FALSE dry-stop), so retry the call a few
// more times before giving up. On resume, the first attempt returns the cached
// result, so this adds no cost to replayed rounds.
async function agentR(prompt, opts, tries = 4) {
  for (let i = 0; i < tries; i++) {
    const r = await agent(prompt, opts)
    if (r) return r
    log(`  ${opts.label || 'agent'}: null (attempt ${i + 1}/${tries}) — likely transient API error, retrying`)
  }
  return null
}

// --- rounds ----------------------------------------------------------------
for (let round = 1; round <= MAX_ROUNDS; round++) {
  phase('Find')
  log(`=== Round ${round}/${MAX_ROUNDS} ===`)
  const KB = kbSummary()
  const dedupeHint = allCandidates.length
    ? `Do NOT re-raise these (find NEW/deeper):\n${allCandidates.map(c => `- [${c.kind}] ${c.title} @ ${c.location}`).join('\n')}`
    : 'No prior candidates.'

  const finders = [
    () => agentR(
`DEDICATED reading-source agent auditing VeriDNS at ${REPO} (round ${round}). Read the RFC docs (${REPO}/rfc/), the mature reference unbound (${REPO}/unbound/, C source), and the VeriDNS Lean sources (${REPO}/VeriDNS/Impl, Spec) AGAINST each other; surface DISCREPANCIES where unbound does a defense/check/normalization/edge-case that VeriDNS omits or does differently and it would be observable and wrong. Read ${REPO}/review/pathmap.md first; focus ON-PATH code. Cite unbound file:line and/or RFC section AND the VeriDNS location, with a concrete runtime experiment.
${KB}
${dedupeHint}
Do NOT edit code. Return candidates (kind 'discrepancy'/'scope-gap'); a few well-substantiated leads beat many shallow ones. Prefer leads that extend or sharpen the KB (e.g. the bailiwick-leniency lead).`,
      { label: `R:read r${round}`, phase: 'Find', model: 'fable', schema: CANDIDATES }),

    () => agentR(
`Spec-auditor for VeriDNS (round ${round}) at ${REPO}. Find WEAK/VACUOUS/OVER-PREMISED theorems — specs loose enough that an observably-wrong impl still satisfies them — and write SPOTs. Read ${REPO}/review/pathmap.md and ${REPO}/review/evidence/oracle-analysis.md first. Deepen these open threads: (a) whether the generated props pin the case fold at all beyond the A=a point (finding 001); (b) ioResumeLoop_sound (Proof/IoResumeSound.lean:2810) ~25 hypotheses — vacuity/coverage of real client queries; (c) whether the heavy IoResumeSound.ioResumeLoop_sound is ever APPLIED (hypotheses discharged) or is terminal; (d) Refinement.resolveWithIO_simulates network arm as an assumption.
Techniques: SPOTs under ${REPO}/review/evidence/spots/ — a SENSIBLE property that SHOULD prove, and a NONSENSE property that should NOT (if it proves, vacuity). You MAY run 'lake env lean <file>' on SPOTs; do NOT run 'lake build' (another stage owns the build tree) and do NOT edit tracked Impl/Proof files.
${KB}
${dedupeHint}
Return candidates (kind 'weak-theorem'); each MUST propose a concrete weaponizable mutant in howToVerify AND note how to distinguish a real semantic catch from proof-script brittleness.`,
      { label: `S:spec r${round}`, phase: 'Find', model: 'fable', schema: CANDIDATES }),

    () => agentR(
`Dynamic differential+pentest agent for VeriDNS (round ${round}) at ${REPO}. Produce OBSERVED behavior, not speculation.
${RIG}
Do NOT rebuild veri-dns (another stage owns the build tree); query the running rig.
1. DIFFERENTIAL: a broad spread (A/AAAA/CNAME/MX/SOA/NS/TXT, NXDOMAIN, empty non-terminals, long/mixed-case names, CNAME chains, malformed/compression-pointer packets) against BOTH resolvers; diff RCODE/answers/TTLs/sections; report divergences with exact dig output.
2. PENTEST: cache poisoning (spoofed-response race via ${REPO}/review/env/spoof.py; out-of-bailiwick glue/answer injection; unrelated records; TTL abuse; id/question mismatch). Report each attack + whether it was accepted or rejected, with output.
PRIORITIZE confirming the KB leads — especially the bailiwick-leniency divergence (grandchild answered from the root IP): reproduce it precisely, and assess whether it is exploitable as a poisoning vector or benign.
${KB}
${dedupeHint}
Do NOT edit code. Return candidates (kind 'discrepancy'/'impl-bug') with actual command output embedded.`,
      { label: `D:dyn r${round}`, phase: 'Find', model: 'fable', schema: CANDIDATES }),
  ]

  const found = (await parallel(finders)).filter(Boolean)
  const finderNotes = found.map(r => r.notes).filter(Boolean)
  const cands = found.flatMap(r => r.candidates || [])
  const fresh = cands.filter(c => { const k = key(c); if (seen.has(k)) return false; seen.add(k); return true })
  allCandidates.push(...fresh)
  log(`Round ${round}: ${cands.length} candidates, ${fresh.length} fresh`)

  // --- mutation synthesis: information-driven, informed by finders + KB -----
  phase('Synthesize')
  const weakFlags = fresh.filter(c => c.kind === 'weak-theorem')
  const diffs = fresh.filter(c => c.kind === 'discrepancy' || c.kind === 'impl-bug')
  const synth = await agent(
`You are the mutation-synthesis agent for VeriDNS at ${REPO} (round ${round}). Design a SMALL set (2-5) of HIGH-VALUE mutations to inject next, informed by everything learned so far. A great mutation is one that makes the implementation OBSERVABLY WRONG in a way a load-bearing spec SHOULD reject — so that "proofs still green + wrong behavior" exposes a bad spec, or "proof breaks" confirms the spec is load-bearing there.
Read the relevant source to make each mutation precise (exact file:line + minimal edit). Use these inputs:
- Weak-theorem flags this round: ${weakFlags.length ? JSON.stringify(weakFlags.map(c => ({t:c.title,loc:c.location,how:c.howToVerify}))) : 'none'}
- Differential/impl discrepancies this round (these show WHERE behavior diverges — often the richest mutation targets): ${diffs.length ? JSON.stringify(diffs.map(c => ({t:c.title,loc:c.location,r:c.rationale.slice(0,200)}))) : 'none'}
- Seed targets: ${SEED_MUTANTS}
${kbSummary()}
CRUCIAL — learn from prior mutant verdicts in the KB: if a mutation was 'proof-caught-brittle' (only a tactic broke, the theorem statement stayed true), design a REFINED version that routes around the incidental catch (e.g. pick letters/names absent from concrete rfl traces) and note that a minimal proof-script repair is warranted to reveal whether the SPEC really constrains it. Do NOT repeat mutations already classified as proof-caught-semantic (those are settled: spec is load-bearing there).
Return 2-5 mutants. For each, fill 'distinguish' with how to tell a semantic catch from brittleness. Prefer mutations that probe the current top leads.`,
    { label: `synth r${round}`, phase: 'Synthesize', model: 'fable', schema: MUTANTS })
  const mutants = (synth?.mutants || []).filter(m => !mutantLog.some(x => x.id === m.id))
  log(`Round ${round}: synthesized ${mutants.length} mutants`)

  // --- verify: serial weaponize (builds), then batched runtime verify -------
  phase('Verify')
  for (const m of mutants) {
    const v = await agent(
`Weaponize-and-verify agent for VeriDNS at ${REPO}. You run SERIALLY in the shared main build tree — you MUST leave it clean (git checkout + rebuild + restart-verid.sh) before returning.
MUTATION: id=${m.id}
  target: ${m.target}
  change: ${m.change}
  expected observable: ${m.expectedObservable}
  ought to catch: ${m.oughtToCatch}
  distinguishing semantic-vs-brittle: ${m.distinguish}
${RIG}
STEPS: (1) apply the minimal mutation; (2) 'lake build' — record green vs broke AND, if broke, the exact file:line + error. (3) If broke, DECIDE: did a theorem STATEMENT become false (proof-caught-semantic → verification is load-bearing here) OR did only a tactic fail while the statement stays true (proof-caught-brittle)? If brittle and the 'distinguish' note says so, attempt a MINIMAL local proof-script repair (a few lines; do NOT re-architect proofs) and rebuild — if it then goes green, this is the real test. (4) If green (with or without a minimal script repair), 'lake build veri-dns' + '${REPO}/review/env/restart-verid.sh', then reproduce the wrong behavior from the attacker ns and compare veri-dns@203.0.113.2:5300 vs unbound@203.0.113.3:5301 (capture dig/tcpdump). (5) Classify per schema; write review/findings/NNN-*.md for a real finding (bad-spec or coverage-gap or impl-bug) with the diff, the build result, and the reproduction+citation. (6) MANDATORY: 'git checkout -- .', 'lake build', '${REPO}/review/env/restart-verid.sh' to restore baseline; confirm git status clean and baseline resolves.
Return the verdict, with a ONE-LINE 'reason' for the knowledge base.`,
      { label: `mut:${m.id}`, phase: 'Verify', model: 'fable', schema: VERDICT })
    if (v) {
      mutantLog.push({ id: m.id, classification: v.classification, reason: (v.reason || '').slice(0, 160) })
      kb.push(`MUTANT ${m.id}: ${v.classification} — ${(v.reason || '').slice(0, 160)}`)
      if (['bad-spec', 'coverage-gap', 'impl-bug'].includes(v.classification)) confirmed.push(v)
      log(`mut ${m.id} -> build=${v.buildGreen} obs=${v.observable} ${v.classification}`)
    }
  }

  // runtime verification of discrepancies/impl-bugs (no build; query the rig)
  const runtime = fresh.filter(c => c.kind === 'discrepancy' || c.kind === 'impl-bug')
  // SERIAL (not parallel): the runtime verifiers share ONE veri-dns instance;
  // running them concurrently cross-contaminated cache-poisoning tests (that is
  // how the loop produced the false-positive 005). Same prompts → Rounds 1-4
  // still replay from cache; only new rounds run, now one-at-a-time on the rig.
  const rverdicts = []
  for (const c of runtime) {
    const v = await agent(
`Runtime-verification agent for VeriDNS at ${REPO}. Confirm or refute with an ACTUAL experiment on the running rig — no speculation.
  title: ${c.title}
  location: ${c.location}
  rationale: ${c.rationale}
  how to verify: ${c.howToVerify}
${RIG}
Do NOT rebuild veri-dns. Reproduce against the rig, capture exact commands+outputs, compare to unbound. Classify impl-bug/coverage-gap/refuted/inconclusive. If confirmed, write review/findings/NNN-*.md (next free 3-digit NNN) with setup, reproduction, and an RFC/unbound citation. Return the verdict with a one-line 'reason'.`,
      { label: `verify:${c.location}`, phase: 'Verify', model: 'fable', schema: VERDICT })
    if (v) rverdicts.push(v)
  }
  for (const v of rverdicts) {
    kb.push(`VERIFY ${v.title}: ${v.classification} — ${(v.reason || '').slice(0, 160)}`)
    if (['bad-spec', 'coverage-gap', 'impl-bug'].includes(v.classification)) confirmed.push(v)
    log(`verify ${v.title} -> ${v.classification}`)
  }

  const newConfirmed = confirmed.length
  const findersRan = found.length > 0   // false => ALL finders errored (API/network); NOT a genuine dry
  const producedSomething = fresh.length > 0 || mutants.length > 0
  if (!findersRan) {
    log(`Round ${round}: ALL finders errored (transient API/network) — INCONCLUSIVE, not counting toward dry`)
  } else if (!producedSomething) {
    dryRounds++; log(`Round ${round}: GENUINE dry (${dryRounds}/${DRY_ROUNDS_TO_STOP}) — finders ran and found nothing new`)
  } else dryRounds = 0
  log(`Round ${round} done. confirmed total: ${newConfirmed}. finder notes: ${finderNotes.join(' || ').slice(0, 300)}`)
  if (dryRounds >= DRY_ROUNDS_TO_STOP) { log('Loop dry — stopping.'); break }
}

log(`Bug hunt complete. confirmed findings this run: ${confirmed.length}`)
return {
  confirmed,
  mutantLog,
  byClass: confirmed.reduce((a, v) => { a[v.classification] = (a[v.classification] || 0) + 1; return a }, {}),
  knowledgeBase: kb,
}
