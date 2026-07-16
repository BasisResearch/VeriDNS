export const meta = {
  name: 'veridns-full-review',
  description: 'End-to-end VeriDNS security & verification review with NO human/main-agent step: preflight (build+FFI fix, axiom audit, execution-path map) -> rig bring-up -> iterative bug-hunt rounds (finders -> mutation synthesis -> SERIAL weaponize -> SERIAL isolated differential verify) -> report synthesis. Loops until genuinely dry.',
  phases: [
    { title: 'Preflight' },
    { title: 'Env' },
    { title: 'Find' },
    { title: 'Synthesize' },
    { title: 'Verify' },
    { title: 'Report' },
  ],
}

// =============================================================================
// VeriDNS full review pipeline.
//
// Everything the review needs is in here. A fresh session runs ONE call:
//   Workflow({ scriptPath: 'review/workflows/full-review.mjs' })
// and gets: a built+runnable resolver, an axiom audit, an execution-path map, a
// live differential rig, N rounds of mutation/differential/pentest bug-hunting,
// and a written REPORT.md. The main agent is NOT in the loop at any point.
//
// Background + rationale: review/HARNESS.md. Rig runbook: review/ENV.md.
// =============================================================================

const REPO = '/home/yiyun/Experiments/VeriDNS'
const MAX_ROUNDS = 12
const DRY_ROUNDS_TO_STOP = 2   // two consecutive GENUINE dry rounds = exhausted

// --- the rig, as every agent must understand it ------------------------------
const RIG = `RIG (full runbook: ${REPO}/review/ENV.md; architecture: ${REPO}/review/HARNESS.md):
- veri-dns (system under test) @203.0.113.2:5300 in netns 'verid'; unbound (reference oracle) @203.0.113.3:5301 in netns 'unbound'.
- nsd authoritative, one per level: root '.' / tld 'test.' / leaf 'example.test.' at 203.0.113.10-12 (root also binds the 5 real root IPs, which veri-dns hardcodes).
- Zones in ${REPO}/review/env/nsd/zones: example.test A=203.0.113.100, host.example.test A=203.0.113.101, www CNAME example.test. Plus rogue-example.test.zone for rogue-ancestor tests.
- attacker/client vantage: netns 'attacker' 192.168.53.99 (dig, tcpdump, spoof.py, crafted responders).
- ADDRESSING (do not "fix" it): the rig is on 203.0.113.0/24 (TEST-NET-3) but the CLIENT is on 192.168.53.99. Forced by two opposing ACLs in Impl/Server.lean: doNotQueryNets (egress) refuses to QUERY 10/8+192.168/16+..., while defaultAcl (ingress) ONLY accepts clients from 127/8, 10/8, 172.16/12, 192.168/16 — an exact subset. So no one subnet can be both. A client on 203.0.113.99 is SILENTLY DROPPED (UDP timeout, TCP accept-then-EOF, empty log). The egress filter is ACTIVE; never set VERI_DNS_ALLOW_LOOPBACK_EGRESS=1. See review/HARNESS.md 2.1.
- The rig lives INSIDE the VM. Reach it ONLY via: ${REPO}/penn-testing/vm/ssh.sh '<cmd>'
- Query veri-dns: ${REPO}/penn-testing/vm/ssh.sh 'ip netns exec attacker dig @203.0.113.2 -p 5300 <name> <type>'
- Query unbound:  ${REPO}/penn-testing/vm/ssh.sh 'ip netns exec attacker dig @203.0.113.3 -p 5301 <name> <type>'
- Load a freshly host-built binary into the VM + restart ONLY veri-dns (fresh cache): ${REPO}/review/env/restart-verid.sh
- Rebuild the whole rig idempotently (after reboot/suspend): ${REPO}/review/env/up.sh`

// --- the hard-won rules. Violating these produced WRONG results before. ------
const RULES = `NON-NEGOTIABLE METHOD RULES (each one exists because violating it produced a wrong result in a prior run — see review/HARNESS.md §5):
1. REVERT PER-FILE, NEVER TREE-WIDE. Use 'git checkout -- <the exact files you edited>'. A tree-wide 'git checkout -- .' is BLOCKED by the harness safety classifier and silently killed ~15 mutations in the earlier run. Never use it.
2. A FINDING IS NOT A FINDING UNTIL UNBOUND DISAGREES. If unbound does the same thing on the same path against the same data, it is the DNS trust model, not a VeriDNS bug. Report it as 'refuted'. (~9 candidates died this way; that is the method working.)
3. RESTART BOTH RESOLVERS BEFORE EVERY DIFFERENTIAL (systemctl restart veridns-verid veridns-ref; sleep 2). A warm unbound (delegation cached) vs a cold veri-dns is NOT a valid comparison — that asymmetry produced a false positive (finding 005).
4. SEMANTIC vs BRITTLE. A mutation is only 'caught' if a theorem STATEMENT became false. If merely a tactic failed while the statement stays true, that is 'proof-caught-brittle' = weak evidence: attempt a MINIMAL local proof-script repair (a few lines; do NOT re-architect) and rebuild. If it then builds green with the impl still observably wrong, that is a real 'bad-spec'.
5. REACHABLE, NOT JUST SOURCE-EDITABLE. A green-building mutant proves a SPEC gap; it is only a BUG if the wrong behavior is reachable at runtime. Prefer wire-level reproductions (dig/tcpdump output).
6. ONLY THE WEAPONIZE STAGE MAY BUILD. Everything else queries the running rig; a stray 'lake build' races the shared build tree.
7. LEAVE IT CLEAN. Every mutation agent MUST end with: per-file 'git checkout --', 'lake build', and '${REPO}/review/env/restart-verid.sh' so the baseline binary is back in the VM, and confirm 'git status' shows the tracked source clean.`

// --- schemas -----------------------------------------------------------------
const CANDIDATE = {
  type: 'object', additionalProperties: false,
  required: ['title', 'kind', 'location', 'rationale', 'howToVerify', 'severity'],
  properties: {
    title: { type: 'string' },
    kind: { type: 'string', enum: ['discrepancy', 'weak-theorem', 'impl-bug', 'scope-gap'] },
    location: { type: 'string', description: 'file:line' },
    rationale: { type: 'string' },
    howToVerify: { type: 'string', description: 'A concrete runtime experiment or mutation that bottoms out in observable behavior.' },
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
    target: { type: 'string', description: 'exact file:line to mutate' },
    change: { type: 'string', description: 'the minimal edit' },
    expectedObservable: { type: 'string', description: 'the wrong runtime behavior + how to observe it on the rig' },
    oughtToCatch: { type: 'string', description: 'which theorem/spec SHOULD reject this if verification is load-bearing' },
    distinguish: { type: 'string', description: 'how to tell a semantic catch from proof-script brittleness; whether a minimal script repair is warranted' },
  },
}
const MUTANTS = {
  type: 'object', additionalProperties: false, required: ['mutants', 'rationale'],
  properties: { mutants: { type: 'array', items: MUTANT }, rationale: { type: 'string' } },
}
const VERDICT = {
  type: 'object', additionalProperties: false,
  required: ['title', 'buildGreen', 'observable', 'unboundDiffers', 'classification', 'reason', 'evidence'],
  properties: {
    title: { type: 'string' },
    buildGreen: { type: 'boolean' },
    observable: { type: 'boolean' },
    unboundDiffers: { type: 'boolean', description: 'Did unbound, on the identical path against identical data with a cold cache, behave CORRECTLY where veri-dns did not? If false, this is NOT a finding (rule 2).' },
    classification: { type: 'string', enum: ['bad-spec', 'coverage-gap', 'impl-bug', 'proof-caught-semantic', 'proof-caught-brittle', 'refuted', 'inconclusive'] },
    reason: { type: 'string', description: 'ONE line for the knowledge base: what caught it, or why it slipped, or why it was refuted.' },
    evidence: { type: 'string', description: 'Actual commands + outputs: build result line, mutation diff, dig/tcpdump comparison vs unbound.' },
    findingFile: { type: 'string' },
  },
}
const PREFLIGHT = {
  type: 'object', additionalProperties: false, required: ['ok', 'summary'],
  properties: {
    ok: { type: 'boolean' },
    summary: { type: 'string' },
    details: { type: 'string' },
  },
}

// --- resilient agent: a null from a transient API error is NOT "no findings" --
async function agentR(prompt, opts, tries = 4) {
  for (let i = 0; i < tries; i++) {
    const r = await agent(prompt, opts)
    if (r) return r
    log(`  ${opts.label || 'agent'}: null (attempt ${i + 1}/${tries}) — likely transient API error, retrying`)
  }
  return null
}

// =============================================================================
// PHASE 0 — PREFLIGHT
// =============================================================================
phase('Preflight')
log('Preflight: build (+FFI fix if needed) -> axiom audit + execution-path map')

// 0a. Build. MUST be first: nothing else can run without a binary. This also
// applies the known-required FFI portability fix (finding 000).
const build = await agentR(
`You are the preflight/build agent for a security review of the VeriDNS verified DNS resolver at ${REPO}.
Goal: leave the repo with (1) all Lean proofs building green, and (2) a RUNNABLE ${REPO}/.lake/build/bin/veri-dns.
Steps:
1. Run 'lake build' (library + proofs) and 'lake build veri-dns' (the executable).
2. KNOWN ISSUE you may hit: the exe fails to LINK with "undefined symbol: arc4random", referenced from veri_dns_random_u16 in ffi/recvfrom.c. arc4random is absent from the Lean toolchain's link sysroot on Linux. If so, FIX IT: replace the arc4random() draw with the kernel CSPRNG via getrandom(2) (<sys/random.h>), falling back to reading /dev/urandom (<fcntl.h>, open/read/close) if getrandom fails. BOTH are cryptographically strong, which is what RFC 5452 §4.3 requires of the query ID — do NOT weaken it to rand()/time(). Then rebuild.
3. Verify the server starts and listens on UDP 5300 (e.g. run it briefly with a timeout).
4. Copy the working binary to ${REPO}/review/veri-dns as a stable baseline reference.
Report ok=true only if the proofs build green AND the binary exists and starts. In 'details', record whether the FFI fix was needed (that is review finding 000) and the exact link error if seen.`,
  { label: 'preflight:build', phase: 'Preflight', model: 'fable', schema: PREFLIGHT })
log(`Preflight build: ok=${build?.ok} — ${build?.summary || 'no result'}`)
if (!build?.ok) {
  log('FATAL: cannot build/run veri-dns; the entire review depends on it. Stopping.')
  return { fatal: 'preflight build failed', build }
}

// 0b + 0c. Axiom audit and the execution-path map. Both read-only; run together.
const [axioms, pathmap] = await parallel([
  () => agentR(
`You are the axiom-audit agent for the VeriDNS review at ${REPO}. The library is built.
Question: do the capstone theorems actually PROVE anything, or do they rest on holes?
1. Grep the whole VeriDNS/ tree for 'sorry', 'admit', bare 'axiom' declarations, and 'unsafe'. Report exactly what you find.
2. Write a scratch Lean file that does 'import VeriDNS' then '#print axioms' for each capstone: ioResumeLoop_sound (there are TWO distinct ones — the root-namespace one in Proof/IoResumeSound.lean and VeriDNS.Proof.NameTree.ioResumeLoop_sound), VeriDNS.Proof.NameTree.resolveWithIO_sound, VeriDNS.Impl.Resolver.scrubAnswerB_excludes_foreign, VeriDNS.Impl.Resolver.scrubAnswerB_authentic, VeriDNS.Proof.Refinement.scrubAnswerB_delivered_model_authentic. Run it with 'lake env lean <file>'.
3. A CLEAN result is: only [propext, Classical.choice, Quot.sound]. Anything else (especially sorryAx or a project-specific axiom) means the proofs have holes and every downstream claim is void.
Report ok=true iff the audit is clean, with the exact axiom lists in 'details'.`,
    { label: 'preflight:axioms', phase: 'Preflight', model: 'fable', schema: PREFLIGHT }),

  () => agentR(
`You are the execution-path-mapping agent for the VeriDNS review at ${REPO}. Produce ${REPO}/review/pathmap.md.
WHY THIS GATES EVERYTHING: a theorem about a definition the server never executes is decorative — it can even be vacuous unnoticed. Later agents use your map to avoid wasting effort on off-path code.
1. Trace the REAL runtime call graph from a UDP packet arriving to the reply being sent: start at VeriDNS/Main.lean, follow into Impl/Server.lean (serverLoop/serveOne), Impl/Resolver.lean (the step* state machine), Impl/Cache.lean, the message codec (Impl/Message, Header, Question, ResourceRecord, RData, DomainName, Parsec, BitPacking, AnswerScrub), and the FFI boundary (ffi/recvfrom.c, Impl/UdpSocket.lean). Name the concrete functions actually invoked.
2. Enumerate every file in VeriDNS/Proof/ and classify its main theorem(s) as ON-PATH (the definitions in the statement are executed by the server), OFF-PATH (never executed — e.g. a ground-truth oracle used only in proofs), or MIXED. One-line justification each, with file:line.
3. List the trust boundary / unverified glue: the FFI C, every @[extern]/opaque, any 'partial' def with no theorem about it, and any modelling gap (e.g. a free-monad 'Prog' model vs real IO).
4. Finish with a "prioritize reading these" list: the 5-10 on-path theorems the real assurance depends on.
Be concrete, cite file:line, do NOT edit any code. Write the file, then report ok=true with a short summary.`,
    { label: 'preflight:pathmap', phase: 'Preflight', model: 'fable', schema: PREFLIGHT }),
])
log(`Preflight axioms: ok=${axioms?.ok} — ${axioms?.summary || 'no result'}`)
log(`Preflight pathmap: ok=${pathmap?.ok} — ${pathmap?.summary || 'no result'}`)

// =============================================================================
// PHASE 0d — ENV / RIG
// =============================================================================
phase('Env')
const env = await agentR(
`You are the environment agent for the VeriDNS review at ${REPO}. Bring up the differential-testing rig and leave it VERIFIED WORKING.
${RIG}
If ${REPO}/review/env/up.sh already exists, it is idempotent: boot the VM if needed ('cd ${REPO}/penn-testing && make vm' in the BACKGROUND; wait until '${REPO}/penn-testing/vm/ssh.sh true' succeeds), then run up.sh, then verify. If the scripts do NOT exist, build the rig from scratch per ${REPO}/review/HARNESS.md §2-3 and write them, plus ${REPO}/review/ENV.md as a copy-pasteable runbook.
Design constraints that MATTER:
- Keep VM RAM ~2 GiB (host budget is 12 GiB total).
- veri-dns hardcodes the real root-server IPs (Main.lean:12-18) and we may NOT patch source, so the fake root nsd must BIND those exact IPs and the resolver netns need /32 on-link routes to them.
- ONE nsd PER LEVEL (root/tld/leaf). A single nsd serving all zones answers grandchild names authoritatively from the root IP, which destroys the differential.
- unbound needs 'local-zone: "test." nodefault' or it returns a built-in RFC 6761 NXDOMAIN for .test and is useless as an oracle.
VERIFY before reporting ok=true: from the attacker ns, BOTH resolvers must answer from the fake hierarchy —
  ssh.sh 'ip netns exec attacker dig @203.0.113.2 -p 5300 example.test A +short'   -> 203.0.113.100
  ssh.sh 'ip netns exec attacker dig @203.0.113.3 -p 5301 example.test A +short'   -> 203.0.113.100
Put the actual dig output in 'details'. If you cannot get the rig up, report ok=false with exactly what failed.`,
  { label: 'env:bringup', phase: 'Env', model: 'fable', schema: PREFLIGHT })
log(`Env: ok=${env?.ok} — ${env?.summary || 'no result'}`)
if (!env?.ok) {
  log('FATAL: rig not up; every finding must be a differential experiment, so we cannot proceed. Stopping.')
  return { fatal: 'rig bring-up failed', build, axioms, pathmap, env }
}

// =============================================================================
// PHASE 1 — ITERATIVE BUG HUNT
// =============================================================================
const key = c => `${c.kind}|${c.location}|${c.title}`.toLowerCase().replace(/\s+/g, ' ').trim()
const seen = new Set()
const confirmed = []
const kb = [
  `PREFLIGHT: build ok. FFI fix needed? see: ${(build.details || '').slice(0, 200)}`,
  `PREFLIGHT: axiom audit ${axioms?.ok ? 'CLEAN' : 'NOT CLEAN — treat all proof-based claims with suspicion'}: ${(axioms?.summary || '').slice(0, 200)}`,
  `PREFLIGHT: execution-path map written to review/pathmap.md — consult it before mutating anything.`,
]
const mutantLog = []
const allCandidates = []
let dryRounds = 0

const kbSummary = () => `KNOWLEDGE BASE (accumulated; build on it, do not re-litigate settled items):
${kb.map(s => '- ' + s).join('\n')}
MUTANTS ALREADY TRIED: ${mutantLog.length ? mutantLog.map(m => `${m.id}=${m.classification}(${m.reason})`).join(' | ') : 'none yet'}`

for (let round = 1; round <= MAX_ROUNDS; round++) {
  phase('Find')
  log(`=== Round ${round}/${MAX_ROUNDS} ===`)
  const KB = kbSummary()
  const dedupeHint = allCandidates.length
    ? `Do NOT re-raise these (find NEW/deeper):\n${allCandidates.map(c => `- [${c.kind}] ${c.title} @ ${c.location}`).join('\n')}`
    : 'No prior candidates.'

  const found = (await parallel([
    // R — reading-source (dedicated agent, per the review plan). Read-only.
    () => agentR(
`DEDICATED reading-source agent auditing VeriDNS at ${REPO} (round ${round}). Read three things AGAINST each other: the RFCs (${REPO}/rfc/), the mature reference implementation unbound (${REPO}/unbound/, C source), and the VeriDNS Lean sources (${REPO}/VeriDNS/Impl, ${REPO}/VeriDNS/Spec).
Find DISCREPANCIES: something unbound does (a defense, check, normalization, edge case) that VeriDNS omits or does differently, in a way that would be OBSERVABLE and WRONG. Read ${REPO}/review/pathmap.md FIRST and focus ON-PATH code; ignore off-path/decorative definitions.
Look at: response validation / RFC 5452 matching, bailiwick and cache-poisoning checks, CNAME chain handling, compression-pointer edge cases, TTL and negative-cache rules (RFC 2181/2308), truncation/TC, case handling, malformed packets, glue acceptance, failover/lame-server handling.
Cite the unbound file:line and/or RFC section AND the VeriDNS location, and give a concrete runtime experiment.
${RULES}
${KB}
${dedupeHint}
Do NOT edit code. Return candidates (kind 'discrepancy'/'scope-gap'); a few well-substantiated leads beat many shallow ones.`,
      { label: `R:read r${round}`, phase: 'Find', model: 'fable', schema: CANDIDATES }),

    // S — spec auditor: vacuity / weak specs / SPOTs.
    () => agentR(
`Spec-auditor for VeriDNS (round ${round}) at ${REPO}. Hunt WEAK, VACUOUS, or OVER-PREMISED theorems — specs loose enough that an observably-wrong implementation still satisfies them. Read ${REPO}/review/pathmap.md first.
Beware the classic dodges: (a) a "law" that is a TAUTOLOGY because the thing it constrains is DEFINED as that law (e.g. compare := fold-equality makes "foldEq -> compareTrue" free); (b) an obligation quantified over a domain that excludes the interesting case; (c) a theorem with so many hypotheses it cannot apply to a real client query — check whether its hypotheses are actually dischargeable at the real entry point, and whether the theorem is ever APPLIED at all (a terminal/orphan theorem is deadweight); (d) an "oracle" premise that assumes the very conclusion (check what is ASSUMED vs PROVEN at M=IO).
Techniques: write SPOTs under ${REPO}/review/evidence/spots/ — a SENSIBLE property that SHOULD be provable, and a NONSENSE property that should NOT be (if it proves, that is vacuity). You MAY run 'lake env lean <file>' on SPOTs. Do NOT run 'lake build' (the weaponize stage owns the build tree) and do NOT edit tracked Impl/Proof files.
${RULES}
${KB}
${dedupeHint}
Return candidates (kind 'weak-theorem'); each MUST name a concrete weaponizable mutant in howToVerify AND say how to distinguish a real semantic catch from proof-script brittleness.`,
      { label: `S:spec r${round}`, phase: 'Find', model: 'fable', schema: CANDIDATES }),

    // D — dynamic differential + pentest against the live rig. No builds.
    () => agentR(
`Dynamic differential + penetration-testing agent for VeriDNS (round ${round}) at ${REPO}. Produce OBSERVED behavior, never speculation.
${RIG}
Do NOT rebuild veri-dns (the weaponize stage owns the build tree); query the running rig.
1. DIFFERENTIAL: a broad spread of queries against BOTH resolvers — A/AAAA/CNAME/MX/SOA/NS/TXT, NXDOMAIN names, empty non-terminals, long and mixed-case names, CNAME chains, malformed/compression-pointer packets, meta QTYPEs, odd opcodes. Diff RCODE, answer set, TTLs, and the authority/additional sections. Report every divergence with exact dig output.
2. PENTEST: cache poisoning attempts — off-path spoofed responses racing the real one (${REPO}/review/env/spoof.py), out-of-bailiwick glue/answer/additional injection, unrelated records piggybacked on answers, TTL abuse, id/question mismatch, rogue-ancestor answers (rogue-example.test.zone), lame/uncooperative servers. For each: state the attack, run it, report accepted-vs-rejected with output.
Cross-reference divergences to RFC sections and to what pathmap.md says the code claims to defend.
${RULES}
${KB}
${dedupeHint}
Do NOT edit VeriDNS code. Return candidates (kind 'discrepancy'/'impl-bug') with the actual command output embedded.`,
      { label: `D:dyn r${round}`, phase: 'Find', model: 'fable', schema: CANDIDATES }),
  ])).filter(Boolean)

  const cands = found.flatMap(r => r.candidates || [])
  const fresh = cands.filter(c => { const k = key(c); if (seen.has(k)) return false; seen.add(k); return true })
  allCandidates.push(...fresh)
  log(`Round ${round}: ${cands.length} candidates, ${fresh.length} fresh`)

  // --- mutation synthesis: informed by this round's findings AND prior verdicts
  phase('Synthesize')
  const weakFlags = fresh.filter(c => c.kind === 'weak-theorem')
  const diffs = fresh.filter(c => c.kind === 'discrepancy' || c.kind === 'impl-bug')
  const synth = await agentR(
`Mutation-synthesis agent for VeriDNS at ${REPO} (round ${round}). Design a SMALL set (2-5) of HIGH-VALUE mutations to inject next.
A great mutation makes the implementation OBSERVABLY WRONG in a way a load-bearing spec SHOULD reject — so "proofs green + wrong behavior" exposes a bad spec, while "proof breaks" positively confirms the spec is load-bearing there. Read the relevant source so each mutation is precise (exact file:line + minimal edit).
Inputs:
- Weak-theorem flags this round: ${weakFlags.length ? JSON.stringify(weakFlags.map(c => ({ t: c.title, loc: c.location, how: c.howToVerify }))) : 'none'}
- Differential/impl discrepancies this round (these show WHERE behavior diverges — often the richest mutation targets): ${diffs.length ? JSON.stringify(diffs.map(c => ({ t: c.title, loc: c.location, r: (c.rationale || '').slice(0, 200) }))) : 'none'}
- Consult ${REPO}/review/pathmap.md: mutate ON-PATH code only.
Good target classes: the RFC 5452 acceptance gate (id/question) and the source/destination match; the bailiwick filters on answers/referrals/additional; the client-delivery scrub AND ITS CALL-SITE (a proven function that is never invoked is a gap); the case fold; TTL clamping and the negative-cache SOA/TTL rules; CNAME chase owner checks; the FFI (query-ID entropy, source reporting) — expect FFI mutants to build green, which demonstrates the unverified boundary.
${kbSummary()}
CRUCIAL — learn from prior verdicts: if a mutation came back 'proof-caught-brittle' (only a tactic broke; the theorem statement stayed true), design a REFINED version that routes around the incidental catch (e.g. pick letters/names absent from concrete rfl-checked traces) and note that a minimal proof-script repair is warranted. Do NOT repeat anything already 'proof-caught-semantic' — that is settled: the spec is load-bearing there.
${RULES}
Return 2-5 mutants; fill 'distinguish' for each.`,
    { label: `synth r${round}`, phase: 'Synthesize', model: 'fable', schema: MUTANTS })
  const mutants = (synth?.mutants || []).filter(m => !mutantLog.some(x => x.id === m.id))
  log(`Round ${round}: synthesized ${mutants.length} mutants`)

  // --- SERIAL weaponize: shared build tree + shared rig. One at a time.
  phase('Verify')
  for (const m of mutants) {
    const v = await agentR(
`Weaponize-and-verify agent for VeriDNS at ${REPO}. You run SERIALLY: you own the shared build tree and the rig for this step, and you MUST leave both clean.
MUTATION: id=${m.id}
  target: ${m.target}
  change: ${m.change}
  expected observable: ${m.expectedObservable}
  ought to catch: ${m.oughtToCatch}
  semantic-vs-brittle guidance: ${m.distinguish}
${RIG}
STEPS:
1. Apply the minimal mutation.
2. 'lake build' — record GREEN vs BROKE, and if broke the exact file:line + error. This is the key proof signal.
3. If BROKE: decide SEMANTIC (a theorem STATEMENT became false -> verification is load-bearing here) vs BRITTLE (only a tactic failed; statement still true). If brittle, attempt a MINIMAL local proof-script repair and rebuild — if it then goes green, continue to step 4; that is the real test.
4. If GREEN (with or without a minimal repair): 'lake build veri-dns', then '${REPO}/review/env/restart-verid.sh' to load the mutant, then reproduce the wrong behavior from the attacker ns. RESTART BOTH RESOLVERS FIRST (rule 3) and compare veri-dns@203.0.113.2:5300 vs unbound@203.0.113.3:5301. Capture dig/tcpdump output. Set unboundDiffers honestly (rule 2).
5. Classify per the schema.
6. If it is a real finding (bad-spec / coverage-gap / impl-bug AND unboundDiffers), write ${REPO}/review/findings/NNN-<slug>.md (next free 3-digit NNN) with: the claim, the mutation diff, the build result proving proofs stayed green, the reproduction commands+output, and an RFC/unbound citation for why it is wrong.
7. MANDATORY CLEANUP (rule 1 + 7): 'git checkout -- <ONLY the exact files you edited>' — NEVER 'git checkout -- .' — then 'lake build' and '${REPO}/review/env/restart-verid.sh'. Confirm 'git status' shows tracked source clean and the baseline resolves correctly.
${RULES}
Return the verdict with a ONE-LINE 'reason' for the knowledge base.`,
      { label: `mut:${m.id}`, phase: 'Verify', model: 'fable', schema: VERDICT })
    if (v) {
      mutantLog.push({ id: m.id, classification: v.classification, reason: (v.reason || '').slice(0, 160) })
      kb.push(`MUTANT ${m.id}: ${v.classification} — ${(v.reason || '').slice(0, 160)}`)
      if (['bad-spec', 'coverage-gap', 'impl-bug'].includes(v.classification) && v.unboundDiffers !== false) confirmed.push(v)
      log(`mut ${m.id} -> build=${v.buildGreen} obs=${v.observable} unboundDiffers=${v.unboundDiffers} ${v.classification}`)
    }
  }

  // --- SERIAL runtime verification (rule 2 + 3). Shared rig: one at a time.
  const runtime = fresh.filter(c => c.kind === 'discrepancy' || c.kind === 'impl-bug')
  for (const c of runtime) {
    const v = await agentR(
`Runtime-verification agent for VeriDNS at ${REPO}. Confirm or REFUTE this suspected bug with an ACTUAL isolated experiment. You run SERIALLY and own the rig for this step.
  title: ${c.title}
  location: ${c.location}
  rationale: ${c.rationale}
  how to verify: ${c.howToVerify}
${RIG}
Do NOT rebuild veri-dns. Before the differential, RESTART BOTH RESOLVERS for cold caches (rule 3) — a warm unbound vs a cold veri-dns is not a valid comparison and has produced a false positive before. Reproduce against the rig, capture exact commands+outputs, and compare to unbound on the identical path against identical data.
Set unboundDiffers honestly: if unbound does the SAME thing, classify 'refuted' (rule 2) — that is a real and valuable result, not a failure.
If confirmed, write ${REPO}/review/findings/NNN-<slug>.md (next free 3-digit NNN) with the setup, reproduction commands+output, and an RFC/unbound citation. If you staged any responder/config in the rig, restore the baseline afterward.
${RULES}
Return the verdict with a one-line 'reason'.`,
      { label: `verify:${c.location}`, phase: 'Verify', model: 'fable', schema: VERDICT })
    if (v) {
      kb.push(`VERIFY ${v.title}: ${v.classification} — ${(v.reason || '').slice(0, 160)}`)
      if (['bad-spec', 'coverage-gap', 'impl-bug'].includes(v.classification) && v.unboundDiffers !== false) confirmed.push(v)
      log(`verify ${v.title} -> ${v.classification} (unboundDiffers=${v.unboundDiffers})`)
    }
  }

  // --- GENUINE dry detection: an API error is NOT "no findings" (rule/HARNESS §5.6)
  const findersRan = found.length > 0
  const producedSomething = fresh.length > 0 || mutants.length > 0
  if (!findersRan) {
    log(`Round ${round}: ALL finders errored (transient API/network) — INCONCLUSIVE, not counting toward dry`)
  } else if (!producedSomething) {
    dryRounds++
    log(`Round ${round}: GENUINE dry (${dryRounds}/${DRY_ROUNDS_TO_STOP}) — finders ran and found nothing new`)
  } else dryRounds = 0
  log(`Round ${round} done. confirmed so far: ${confirmed.length}`)
  if (dryRounds >= DRY_ROUNDS_TO_STOP) { log('Loop genuinely dry — stopping.'); break }
}

// =============================================================================
// PHASE 2 — REPORT SYNTHESIS
// =============================================================================
phase('Report')
const report = await agentR(
`You are the report-synthesis agent for the VeriDNS security & verification review at ${REPO}. Write ${REPO}/review/REPORT.md — the canonical deliverable. No one will hand-edit it after you.
THE QUESTION THE REPORT MUST ANSWER: is VeriDNS's "verified" claim LOAD-BEARING — does the proof actually rule out bugs — or is correctness merely inherited from mirroring a mature resolver? A reader must be able to decide whether to TRUST the implementation.
Inputs to read and synthesize:
- ${REPO}/review/findings/ — every finding file produced this run (agent-assigned numbers may COLLIDE; your report is the canonical index, so disambiguate).
- ${REPO}/review/pathmap.md — on-path vs off-path classification.
- ${REPO}/review/HARNESS.md — method and its constraints.
- Preflight: build ${JSON.stringify((build.summary || '').slice(0, 300))}; axiom audit ${JSON.stringify((axioms?.summary || '').slice(0, 300))}.
- Accumulated knowledge base and verdicts:
${kbSummary()}
Required sections:
1. **Bottom line / trust verdict.** Be decisive and honest. Separate what IS proven and load-bearing (cite the 'proof-caught-semantic' results — mutations that broke a real theorem statement) from what is NOT (bad-specs where a wrong impl built green; coverage-gaps in unverified glue). State plainly what a reader may and may not infer.
2. **Findings**, grouped by severity/class, each with: what it is, the trigger, a link to the reproduction, and an RFC/unbound citation for why it is undesirable. For every bad-spec, state the injected mutation that slipped through the proofs.
3. **Refuted candidates** — keep them, with why (unbound did the same => trust model, not a bug). This is evidence of rigor; do not hide it.
4. **Verification architecture** — which verified code the running server actually executes; flag off-path/decorative verification so the reader deprioritizes it.
5. **Navigation guide** — a prioritized reading list for a human reviewer.
6. **Method + caveats** — including any coverage gaps (mutations that could not be evaluated, rounds degraded by API errors, findings not isolation-verified).
Distinguish clearly between claims verified by an ISOLATED differential re-run and claims resting only on a single agent's observation. Do not overstate: a green-building mutant proves a SPEC gap; it is a BUG only if the wrong behavior is reachable at runtime.
Report ok=true with a one-paragraph summary of the verdict you wrote.`,
  { label: 'report:synthesis', phase: 'Report', model: 'fable', schema: PREFLIGHT })
log(`Report: ok=${report?.ok} — ${report?.summary || 'no result'}`)

log(`Full review complete. confirmed findings: ${confirmed.length}`)
return {
  preflight: { build, axioms, pathmap, env },
  confirmed,
  mutantLog,
  byClass: confirmed.reduce((a, v) => { a[v.classification] = (a[v.classification] || 0) + 1; return a }, {}),
  knowledgeBase: kb,
  report,
}
