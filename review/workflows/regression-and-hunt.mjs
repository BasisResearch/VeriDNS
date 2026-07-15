export const meta = {
  name: 'veridns-regression-and-hunt',
  description: 'Re-validate the prior review\'s findings against the new upstream (26b5849), then continue hunting NEW bugs in the newly-added surface (TCP, EDNS0, QNAME-minimisation, adequacy capstones). Preflight -> rig -> regression -> iterative rounds -> report.',
  phases: [
    { title: 'Preflight' },
    { title: 'Env' },
    { title: 'Regression' },
    { title: 'Find' },
    { title: 'Synthesize' },
    { title: 'Verify' },
    { title: 'Report' },
  ],
}

// =============================================================================
// VeriDNS regression + continued bug hunt.
//
//   Workflow({ scriptPath: 'review/workflows/regression-and-hunt.mjs' })
//
// Context that makes this run DIFFERENT from full-review.mjs:
//  - The prior review ran against 8e4e16d. Upstream is now 26b5849, a single
//    large commit that EXPLICITLY remediates this review (docs/remediation-plan.md
//    claims "every review finding is now fixed, theorem-pinned, or scoped out").
//    Phase 'Regression' exists to TEST THAT CLAIM, finding by finding.
//  - Upstream ALSO added large new surface the prior review never saw: DNS-over-TCP
//    (Impl/TcpFraming.lean, Proof/ServeTcp.lean), EDNS0 (Impl/Edns.lean),
//    QNAME-minimisation (DomainName.minimisedName), and new "adequacy"/completeness
//    capstones. New code is where new bugs are; the hunt rounds target it.
//  - The rig is RENUMBERED 10.53.0.0/24 -> 203.0.113.0/24. Upstream added a
//    do-not-query egress filter (Server.lean:336 doNotQueryNets) that BLOCKS
//    10/8. On the old rig addresses veri-dns cannot reach its own auth servers
//    and EVERY test fails spuriously. TEST-NET-3 is not in the filter, so the
//    filter stays in its SHIPPED state (do NOT paper over it with
//    VERI_DNS_ALLOW_LOOPBACK_EGRESS=1 — that would mask real egress bugs).
//
// Background: review/HARNESS.md. Rig runbook: review/ENV.md.
// =============================================================================

const REPO = '/home/yiyun/Experiments/VeriDNS'
const MAX_ROUNDS = 12
const DRY_ROUNDS_TO_STOP = 2

const NET = '203.0.113'
const RIG = `RIG (runbook: ${REPO}/review/ENV.md; architecture: ${REPO}/review/HARNESS.md):
- The rig is RENUMBERED to ${NET}.0/24 (TEST-NET-3). The old docs/scripts say 10.53.0.0/24 — that is STALE. Upstream's doNotQueryNets (VeriDNS/Impl/Server.lean:336) blocks 10/8, so on the old addresses veri-dns refuses to query its own auth servers. ${NET}.0/24 is NOT filtered, so the shipped egress filter stays ACTIVE and honest.
- veri-dns (system under test) @${NET}.2:5300 in netns 'verid'; unbound (reference oracle) @${NET}.3:5301 in netns 'unbound'.
- nsd authoritative, one per level: root '.' / tld 'test.' / leaf 'example.test.' at ${NET}.10/.11/.12 (root ALSO binds the 5 real root IPs, which veri-dns hardcodes in Main.lean).
- Zones in ${REPO}/review/env/nsd/zones: example.test A=${NET}.100, host.example.test A=${NET}.101, www CNAME example.test. Plus rogue-example.test.zone.
- attacker/client vantage: netns 'attacker' ${NET}.99 (dig, tcpdump, spoof.py, crafted responders).
- The rig lives INSIDE the VM. Reach it ONLY via: ${REPO}/penn-testing/vm/ssh.sh '<cmd>'
- Query veri-dns: ${REPO}/penn-testing/vm/ssh.sh 'ip netns exec attacker dig @${NET}.2 -p 5300 <name> <type>'
- Query unbound:  ${REPO}/penn-testing/vm/ssh.sh 'ip netns exec attacker dig @${NET}.3 -p 5301 <name> <type>'
- veri-dns now speaks TCP too — test it: dig +tcp @${NET}.2 -p 5300 ...
- Load a freshly host-built binary into the VM + restart ONLY veri-dns (fresh cache): ${REPO}/review/env/restart-verid.sh
- Rebuild the whole rig idempotently: ${REPO}/review/env/up.sh`

const RULES = `NON-NEGOTIABLE METHOD RULES (each exists because violating it produced a WRONG result in a prior run — review/HARNESS.md §5):
1. REVERT PER-FILE, NEVER TREE-WIDE. 'git checkout -- <the exact files you edited>'. A tree-wide 'git checkout -- .' is BLOCKED by the harness safety classifier and silently killed ~15 mutations before. Never use it.
2. A FINDING IS NOT A FINDING UNTIL UNBOUND DISAGREES. If unbound does the same thing on the same path against the same data, it is the DNS trust model, not a VeriDNS bug -> 'refuted'. (~9 candidates died this way; that is the method working.)
3. RESTART BOTH RESOLVERS BEFORE EVERY DIFFERENTIAL (systemctl restart veridns-verid veridns-ref; sleep 2). A warm unbound vs a cold veri-dns is NOT a comparison — that asymmetry manufactured false positive 005.
4. SEMANTIC vs BRITTLE. A mutation is 'caught' only if a theorem STATEMENT became false. If merely a tactic broke while the statement stays true, that is 'proof-caught-brittle' = weak evidence: attempt a MINIMAL local proof-script repair (a few lines; do NOT re-architect) and rebuild. If it then builds green with the impl still observably wrong, that is a real 'bad-spec'. (This is how 014 was settled.)
5. REACHABLE, NOT JUST SOURCE-EDITABLE. A green-building mutant proves a SPEC gap; it is a BUG only if the wrong behavior is reachable at runtime. Prefer wire-level repros.
6. ONLY THE WEAPONIZE STAGE MAY BUILD. Everything else queries the running rig; a stray 'lake build' races the shared build tree.
7. LEAVE IT CLEAN. Every mutation agent MUST end with per-file 'git checkout --', 'lake build', and '${REPO}/review/env/restart-verid.sh', and confirm 'git status' shows tracked source clean.
8. SERIALIZE RIG ACCESS. You may be one of several agents; but the workflow only ever runs ONE rig-touching agent at a time. Never background a long rig job and return.`

// --- schemas -----------------------------------------------------------------
const CANDIDATE = {
  type: 'object', additionalProperties: false,
  required: ['title', 'kind', 'location', 'rationale', 'howToVerify', 'severity'],
  properties: {
    title: { type: 'string' },
    kind: { type: 'string', enum: ['discrepancy', 'weak-theorem', 'impl-bug', 'scope-gap'] },
    location: { type: 'string', description: 'file:line' },
    rationale: { type: 'string' },
    howToVerify: { type: 'string', description: 'A concrete runtime experiment or mutation bottoming out in observable behavior.' },
    severity: { type: 'string', enum: ['critical', 'high', 'medium', 'low', 'info'] },
  },
}
const CANDIDATES = {
  type: 'object', additionalProperties: false, required: ['candidates', 'notes'],
  properties: { candidates: { type: 'array', items: CANDIDATE }, notes: { type: 'string' } },
}
const REGRESSION_ITEM = {
  type: 'object', additionalProperties: false,
  required: ['finding', 'status', 'evidence', 'reason'],
  properties: {
    finding: { type: 'string', description: 'e.g. "015 — . NS bricks resolution"' },
    status: {
      type: 'string',
      enum: ['patched-verified', 'patched-code-only', 'still-present', 'partially-fixed', 'scoped-out-acceptable', 'scoped-out-disputed', 'regressed-new-bug', 'inconclusive'],
      description: 'patched-verified = the old repro no longer reproduces ON THE RIG. patched-code-only = the code clearly changed but you could not run the repro. still-present = the old repro STILL reproduces and unbound still disagrees.',
    },
    evidence: { type: 'string', description: 'Exact commands + outputs. For patched-verified, show the OLD repro now behaving correctly AND unbound agreeing.' },
    reason: { type: 'string', description: 'ONE line for the knowledge base.' },
    fixQuality: { type: 'string', description: 'Is the fix load-bearing (pinned by a theorem that would go red if reverted) or just an impl patch nothing constrains? Note any NEW weakness the fix introduced.' },
  },
}
const REGRESSION = {
  type: 'object', additionalProperties: false, required: ['items', 'notes'],
  properties: {
    items: { type: 'array', items: REGRESSION_ITEM },
    notes: { type: 'string' },
    newCandidates: { type: 'array', items: CANDIDATE, description: 'Any NEW bug you tripped over while regression-testing. Do not chase far; just record.' },
  },
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
    unboundDiffers: { type: 'boolean', description: 'Did unbound, on the identical path against identical data with a COLD cache, behave CORRECTLY where veri-dns did not? If false this is NOT a finding (rule 2).' },
    classification: { type: 'string', enum: ['bad-spec', 'coverage-gap', 'impl-bug', 'proof-caught-semantic', 'proof-caught-brittle', 'refuted', 'inconclusive'] },
    reason: { type: 'string', description: 'ONE line for the knowledge base.' },
    evidence: { type: 'string', description: 'Actual commands + outputs: build result line, mutation diff, dig/tcpdump comparison vs unbound.' },
    findingFile: { type: 'string' },
  },
}
const PREFLIGHT = {
  type: 'object', additionalProperties: false, required: ['ok', 'summary'],
  properties: { ok: { type: 'boolean' }, summary: { type: 'string' }, details: { type: 'string' } },
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
log('Preflight: build -> axiom audit + FRESH execution-path map (the tree changed massively)')

const build = await agentR(
`You are the preflight/build agent for a security review of the VeriDNS verified DNS resolver at ${REPO} (branch review/bug-hunt-2, upstream commit 26b5849).
Goal: leave the repo with (1) all Lean proofs building green, and (2) a RUNNABLE ${REPO}/.lake/build/bin/veri-dns.
1. Run 'lake build' and 'lake build veri-dns'. A build may already be warm/complete — check before starting a fresh one.
2. NOTE: the arc4random link failure (old finding 000) is FIXED upstream — ffi/recvfrom.c now uses getrandom(2) with a /dev/urandom fallback under '#ifdef __linux__'. If you nonetheless hit a link error, fix it the same way and say so.
3. Verify the server starts and listens on UDP 5300 (run it briefly with a timeout). Upstream also added TCP — note whether it listens on TCP 5300 too.
4. Copy the working binary to ${REPO}/review/veri-dns as the baseline reference.
Report ok=true only if proofs build green AND the binary exists and starts. Put the exact 'lake build' summary line and the listen evidence in 'details'.`,
  { label: 'preflight:build', phase: 'Preflight', model: 'fable', schema: PREFLIGHT })
log(`Preflight build: ok=${build?.ok} — ${build?.summary || 'no result'}`)
if (!build?.ok) {
  log('FATAL: cannot build/run veri-dns; the entire review depends on it. Stopping.')
  return { fatal: 'preflight build failed', build }
}

const [axioms, pathmap] = await parallel([
  () => agentR(
`You are the axiom-audit agent for the VeriDNS review at ${REPO}. The library is built.
Question: do the capstone theorems actually PROVE anything, or do they rest on holes? Upstream (26b5849) added NEW capstones since the last audit — find them, do not just check the old list.
1. Grep the whole VeriDNS/ tree for 'sorry', 'admit', bare 'axiom' declarations, and 'unsafe'. Report exactly what you find, with file:line.
2. Write a scratch Lean file (NOT under VeriDNS/) that does 'import VeriDNS' then '#print axioms' for each capstone. Cover at least: VeriDNS.Proof.NameTree.resolveWithIO_sound, both ioResumeLoop_sound's (Proof/IoResumeSound.lean and Proof/NameTree.lean), VeriDNS.Impl.Resolver.scrubAnswerB_excludes_foreign, scrubAnswerB_authentic, VeriDNS.Proof.Refinement.scrubAnswerB_delivered_model_authentic, PLUS the NEW ones in Proof/ResolveWithIOSound.lean, Proof/ServeSound.lean, Proof/ServeAdequacy.lean, Proof/SpineAdequacy.lean, Proof/ServeTcp.lean, Proof/NameTreeComplete.lean, Proof/SentMinimised.lean. Grep those files for their top-level theorems first.
   Run with 'lake env lean <file>'.
3. CLEAN = only [propext, Classical.choice, Quot.sound]. Anything else (especially sorryAx or a project-specific axiom) means the proofs have holes and every downstream claim is void.
Report ok=true iff clean. Put the exact per-theorem axiom lists in 'details'.`,
    { label: 'preflight:axioms', phase: 'Preflight', model: 'fable', schema: PREFLIGHT }),

  () => agentR(
`You are the execution-path-mapping agent for the VeriDNS review at ${REPO}. REWRITE ${REPO}/review/pathmap.md — the existing file is STALE (it describes commit 8e4e16d; upstream 26b5849 rewrote large parts and ADDED DNS-over-TCP, EDNS0, QNAME-minimisation, and new adequacy/completeness capstones).
WHY THIS GATES EVERYTHING: a theorem about a definition the server never executes is decorative and can be vacuous unnoticed. Later agents use your map to avoid wasting effort off-path.
1. Trace the REAL runtime call graph from a UDP (and now TCP) packet arriving to the reply being sent: VeriDNS/Main.lean -> Impl/Server.lean (serverLoop/serveOne/serveDatagram, the TCP path, doNotQueryNets/blockedEgress) -> Impl/Resolver.lean (the step* state machine, extractCname, scrubAnswerB, bailiwickRaws, minimisedName) -> Impl/Cache.lean -> codec (Impl/Message, Header, Question, ResourceRecord, RData, DomainName, Parsec, BitPacking, AnswerScrub, Edns, TcpFraming) -> FFI (ffi/recvfrom.c, Impl/UdpSocket.lean). Name the concrete functions actually invoked.
2. Enumerate EVERY file in VeriDNS/Proof/ and classify its main theorem(s) ON-PATH / OFF-PATH / MIXED, one-line justification each with file:line. Call out theorems that are TERMINAL ORPHANS (proven but never applied anywhere) — that is deadweight verification (old finding 025 said IoResumeSound.ioResumeLoop_sound was one; re-check whether that is still true).
3. List the trust boundary / unverified glue: the FFI C, every @[extern]/opaque, any 'partial' def with no theorem, and any modelling gap.
4. IMPORTANT — say specifically which of the NEW surface (TCP framing, EDNS0/OPT, QNAME-minimisation, egress filter) is actually covered by a theorem vs merely implemented. New code with no proof is the richest hunting ground for the rounds that follow.
5. Finish with a "prioritize reading these" list: the 5-10 on-path theorems the real assurance depends on.
Be concrete, cite file:line, do NOT edit any code outside review/. Write the file, then report ok=true with a short summary.`,
    { label: 'preflight:pathmap', phase: 'Preflight', model: 'fable', schema: PREFLIGHT }),
])
log(`Preflight axioms: ok=${axioms?.ok} — ${axioms?.summary || 'no result'}`)
log(`Preflight pathmap: ok=${pathmap?.ok} — ${pathmap?.summary || 'no result'}`)

// =============================================================================
// PHASE 0d — ENV / RIG (renumbered)
// =============================================================================
phase('Env')
const env = await agentR(
`You are the environment agent for the VeriDNS review at ${REPO}. Bring up the differential-testing rig and leave it VERIFIED WORKING.
${RIG}
THE ONE BIG CHANGE THIS RUN — RENUMBERING. The scripts under ${REPO}/review/env/ currently hardcode 10.53.0.0/24. Upstream added an egress filter (VeriDNS/Impl/Server.lean:336 'doNotQueryNets') that blocks 0/8, 127/8, 10/8, 100.64/10, 169.254/16, 172.16/12, 192.168/16, 240/4. The rig's auth servers at 10.53.0.x are therefore UNREACHABLE to veri-dns and every test would fail spuriously.
FIX: renumber the whole rig 10.53.0. -> ${NET}. (TEST-NET-3, not in the filter). Do NOT set VERI_DNS_ALLOW_LOOPBACK_EGRESS=1 to work around it — that disables the shipped filter and would mask real egress bugs. We want the filter ACTIVE and honest.
Steps:
1. Update every file under ${REPO}/review/env/ that mentions 10.53.0 (vm-up.sh, up.sh, down.sh, query.sh, restart-verid.sh, nsd/*.conf, nsd/zones/*, unbound/unbound.conf, spoof.py, rogue_auth.py, fatauth_responder.py, qr0responder.py, VERIFICATION.txt). Keep the 5 real root IPs (198.41.0.4, 199.9.14.201, 192.33.14.30, 199.7.91.13, 192.203.230.10) EXACTLY as they are — veri-dns hardcodes them and the fake root must keep binding them. Do not renumber those.
2. Boot the VM if needed: 'cd ${REPO}/penn-testing && make vm' in the BACKGROUND, then wait until '${REPO}/penn-testing/vm/ssh.sh true' succeeds. It may already be up — check first.
3. Run ${REPO}/review/env/up.sh (idempotent).
4. Update ${REPO}/review/ENV.md and the addresses table in ${REPO}/review/HARNESS.md §2 to the new subnet, and note WHY (the egress filter) so the next reader is not confused.
Design constraints that MATTER:
- Keep VM RAM ~2 GiB (host budget 12 GiB total).
- veri-dns hardcodes the real root IPs (Main.lean) and we may NOT patch source, so the fake root nsd must BIND those exact IPs; resolver netns need /32 on-link routes to them.
- ONE nsd PER LEVEL (root/tld/leaf). A single nsd serving all zones answers grandchild names authoritatively from the root IP and destroys the differential.
- unbound needs 'local-zone: "test." nodefault' or it returns a built-in RFC 6761 NXDOMAIN for .test and is useless as an oracle.
VERIFY before reporting ok=true — from the attacker ns, BOTH resolvers answer from the fake hierarchy:
  ssh.sh 'ip netns exec attacker dig @${NET}.2 -p 5300 example.test A +short'   -> ${NET}.100
  ssh.sh 'ip netns exec attacker dig @${NET}.3 -p 5301 example.test A +short'   -> ${NET}.100
  and host.example.test A -> ${NET}.101 on both.
ALSO verify TCP works on veri-dns (dig +tcp @${NET}.2 -p 5300 example.test A) since upstream added it — record the result either way.
Put the actual dig output in 'details'. If you cannot get the rig up, report ok=false with exactly what failed.`,
  { label: 'env:bringup', phase: 'Env', model: 'fable', schema: PREFLIGHT })
log(`Env: ok=${env?.ok} — ${env?.summary || 'no result'}`)
if (!env?.ok) {
  log('FATAL: rig not up; every finding must be a differential experiment. Stopping.')
  return { fatal: 'rig bring-up failed', build, axioms, pathmap, env }
}

// =============================================================================
// PHASE 1 — REGRESSION: does the remediation claim hold?
// =============================================================================
phase('Regression')
log('Regression: testing docs/remediation-plan.md\'s claim that every prior finding is fixed')

// Batches are THEMED so each agent can reuse one rig setup across its items.
// They run SERIALLY: each owns the rig for its turn (rule 8 / HARNESS §5.2).
const BATCHES = [
  {
    id: 'availability',
    title: 'Availability / liveness cluster (soundness proofs cannot see these)',
    items: `- 015 — a single 'dig . NS' permanently bricks resolution (SERVFAIL, zero egress, for every root-descending name until restart). THE headline bug. Upstream claims ROOT CAUSE FIXED (stepFindServers now falls back to sbelt when 'glue.isEmpty && mc == 0', Impl/Resolver.lean ~:321).
- 017 — FFI did one recvmsg then close(fd), so one junk datagram dropped the real reply. Upstream claims FIXED: ffi/recvfrom.c ~:244 now loops with a 2s deadline and skips datagrams whose sender != dest. Test with a junk flood.
- 026 / 046 — upstream REFUSED/FORMERR-with-authority aborts resolution and SERVFAILs instead of failing over to a sibling server.
- 035 — multi-homed nameserver failover broken: only the FIRST NS address is ever retried.
- 041 / 045 — a bare empty NOERROR from the first-tried (lame) server is taken at face value: veri-dns returns a spurious NODATA for a name that EXISTS; unbound fails over and answers. 045 was CONFIRMED vs unbound and is a WRONG ANSWER, not just availability.
- 040 — referral with AA=1 not followed -> NODATA.`,
  },
  {
    id: 'poisoning',
    title: 'Cache injection / poisoning',
    items: `- 004 — answer caching kept any in-bailiwick SUBDOMAIN of the qname (isAncestorB) where unbound strips to owner==qname. Upstream claims FIXED: Impl/AnswerScrub.lean now computes 'reachableNamesB' (qname + CNAME-chain targets) and scrubAnswerB keeps only owners in that set. Re-run the old repro: inject 'sub.example.test A 6.6.6.6' piggybacked on an example.test answer; it must NOT be cached/served.
- 012 / 013 — negative-cache SOA owner unconstrained: a rogue server's NXDOMAIN with an SOA owned by poison.attacker.test was cached & served; unbound scrubs it (AUTHORITY:0). Upstream claims FIXED (+ a 'scrubAuthorityB' in deliveredResponse for the residual).
- 047 — attacker-injected OUT-OF-BAILIWICK ADDITIONAL A records delivered to the client verbatim; unbound strips them. NOT in the remediation plan — likely still present. Check hard.
- 019 — CNAME conduit: out-of-bailiwick answer injection through a CNAME.
- 038 — promiscuous answer-section NS redirects a subtree.
- 039 — CNAME target NXDOMAIN poisons the alias for all types.
- 024 / 027 / 028 — negcache AA-blindness; DS apex answered from child zone; cache hit serves first-writer owner case.
- 018 / 020 — network path leaks upstream authority/additional unscrubbed; QTYPE=ANY bypasses the scrub.`,
  },
  {
    id: 'egress',
    title: 'Egress control / SSRF (2nd-most-serious cluster)',
    items: `- 036 — extractCname followed the FIRST type-5 record with NO owner check, so an off-owner CNAME steered veri-dns's egress to an attacker-chosen target. Upstream claims FIXED: Impl/Resolver.lean:48 now requires 'DomainName.nameEqCI (RRParse.rrName rr) sname'. Re-run: an answer carrying 'attacker.chosen. CNAME target.' must NOT be chased.
- 021 — no do-not-query filter: veri-dns would query 127.0.0.1:53 / private addresses. Upstream claims DONE: Impl/Server.lean:336 doNotQueryNets + blockedEgress. VERIFY IT IS ACTUALLY ON: the rig is on ${NET}.0/24 precisely so the filter stays active. Test by delegating a zone to a nameserver whose glue A points at 127.0.0.1 (and at 10.0.0.1, 192.168.1.1) and confirm veri-dns emits NO packet there (tcpdump) while still behaving sanely. ALSO check the VERI_DNS_ALLOW_LOOPBACK_EGRESS=1 bypass exists and is OFF by default.
- 022 — no QNAME minimisation (full name leaked to every server). Upstream ADDED it (DomainName.minimisedName, Resolver.lean ~:459). Verify with tcpdump on the auth ns: does the root actually see only 'test.' rather than 'host.example.test'? And does minimisation break resolution anywhere (RFC 9156)?`,
  },
  {
    id: 'parser',
    title: 'Parser / malformed-packet conformance',
    items: `- 009b — QNAME parser dereferenced a compression pointer INTO the 12-byte header, fabricated the root name and ran a full recursion; unbound returns FORMERR. Upstream claims FIXED: Impl/DomainName.lean:30 now errors 'compression pointer into the header, forward, or self (RFC 1035 §4.1.4)'. Re-run the old wire repro.
- 037 — name-bearing RDATA (MX/SRV/NS/CNAME) forwarded verbatim with compression pointers intact, corrupting the embedded name off-path. Upstream claims FIXED.
- 010b — undecodable query silently dropped instead of FORMERR. Upstream claims FIXED.
- 029 — MX rdata compression pointer forwarded corrupt.
- 042 — query with non-empty answer/authority sections resolved instead of FORMERR.
- 023 — opcode 3-7 silently dropped, no NOTIMP. Upstream appears to have added 'supportsQueryKind' -> notImplemented (Impl/Server.lean:120) — verify on the wire.
- 044b — meta/pseudo QTYPEs (OPT/MAILA/MAILB/AXFR/IXFR) recursed as ordinary types; veri-dns emitted a malformed OPT-typed query on the wire.
- 030 — acceptResponse checks ONLY id + question, never QR or OPCODE. I checked the new source: Impl/Server.lean:51-55 STILL only checks id + questionMatches. NOT in the remediation plan. This is very likely STILL PRESENT — confirm it and try to weaponize it (a crafted packet with QR=0 or a wrong opcode that matches id+question).
- 033 — multi-question FORMERR echoes questions with qd=2, ra=1.`,
  },
  {
    id: 'transport',
    title: 'Transport / truncation — NOTE: upstream ADDED TCP + EDNS0, so these are re-scoped',
    items: `- 006 / 015b — no DNS-over-TCP at all (RFC 7766 §5 MUST). The remediation plan says "scoped out", but the commit message says TCP LANDED (Impl/TcpFraming.lean, Proof/ServeTcp.lean, Proof/ServeSequence.lean). Determine the truth: does veri-dns accept TCP queries AND fall back to TCP on an upstream TC=1? Test both directions.
- 016 / 009a — no EDNS0 / OPT ignored. Plan says "scoped out" but Impl/Edns.lean now exists and Resolver.lean:486 emits an OPT RR with 'Edns.advertisedUdpSize'. Determine the truth on the wire; check the advertised size is sane and that a client's OPT is honored.
- 031 — upstream UDP recv buffer hard-capped at 512B silently clipped larger TC=0 responses. Upstream bumped VERI_DNS_UPSTREAM_BUFSIZE to 1232 (ffi/recvfrom.c:1). Verify a >512B, <=1232B response now survives — and check what happens at >1232B.
- 032 — the client's TC bit reflected into local replies.
- 043 / 044a — truncateUdp self-inflicts TC and drops authority; the delivered-header spec leaves TC UNCONSTRAINED (forcing TC=1 built green and bricked all resolution).`,
  },
  {
    id: 'provenance',
    title: 'Spec provenance / load-bearingness (mutation-based — this batch MAY build)',
    items: `You are the ONLY regression batch permitted to run 'lake build' (rule 6). Re-test whether the fixes are actually PINNED by theorems, or are just impl patches nothing constrains — i.e. would the fix survive review if someone reverted it? Revert-the-fix mutations are the sharpest tool here.
- 001 / 014 — case-fold spec was not load-bearing via the RFC-generated props; a surgical 'W' under-fold survived a coordinated repair. Upstream claims FIXED: 'namespace_casefold_exact'/'namespace_compare_complete', all five case predicates via-discharged, and claims "the W under-fold mutant confirmed red at foldCaseByte_casefold_exact". VERIFY THAT CLAIM by re-running the W under-fold mutation. This is the single best test of whether the remediation is real.
- 002 — query-ID entropy is unverified extern glue; a constant-ID mutant built green. Upstream claims (a)+(b) done and added VeriDNS/Test/IdEntropy.lean. Does a constant-ID mutant NOW break something (a test, a build), or does it still build green? Note: 048 established the DEPLOYED binary really does randomize txid+source port; the finding is only about what the PROOF enforces.
- 008 — TC=1 gate on negative caching bound to no obligation. Upstream claims 'storeNegativeIfCacheable_truncated' + 'replyForResolution_truncated_cache_unchanged' now pin it. Try reverting the gate and see if the build goes red.
- 025 — Proof/IoResumeSound.lean's ioResumeLoop_sound (~25 hypotheses) is a TERMINAL ORPHAN: proven but never applied. Is it still an orphan in 26b5849? Check whether the new ResolveWithIOSound/ServeSound capstones actually consume it.
- 034 — RFC 2181 lowest-TTL rule pinned to a phantom value, blind to the real one.
- 044a — the delivered-header spec leaves TC unconstrained. Upstream claims a fix; test by forcing TC=1 in the delivered header and seeing if the build goes red.
- NEW: the fixes themselves. For 004 (reachableNamesB), 036 (nameEqCI owner check), 013 (scrubAuthorityB), 021 (blockedEgress): revert each ONE fix and check whether ANY theorem goes red. A fix that no theorem pins is a fix that can silently regress — that is itself a coverage-gap finding worth reporting.`,
  },
]

const regressionResults = []
for (const b of BATCHES) {
  const canBuild = b.id === 'provenance'
  const r = await agentR(
`REGRESSION agent for the VeriDNS review at ${REPO}. You run SERIALLY and OWN THE RIG for this step.
THE SITUATION: a prior security review (branch review/bug-hunt, commit 8e4e16d) found ~53 issues. Upstream has since shipped ONE large remediation commit (26b5849) with ${REPO}/docs/remediation-plan.md claiming **"every review finding is now fixed, theorem-pinned, or scoped out with rationale."** YOUR JOB IS TO TEST THAT CLAIM for your batch. Be skeptical and empirical: a claim in a markdown file is not evidence. A code change that looks right is weak evidence. The old reproduction failing to reproduce ON THE RIG is evidence.
YOUR BATCH — ${b.title}:
${b.items}

METHOD, per item:
1. Read the ORIGINAL finding file in ${REPO}/review/findings/ (match by number; note numbers COLLIDE — there are two 004s, 009s, 010s, 015s, 018s, 044s — read all matches). It has the original repro. ${REPO}/review/REPORT.md is the canonical index. Also read the relevant section of ${REPO}/docs/remediation-plan.md for what upstream CLAIMS.
2. Read the CURRENT source at the cited location to see what actually changed.
3. RE-RUN THE ORIGINAL REPRODUCTION on the rig. Restart BOTH resolvers first (rule 3). Compare to unbound (rule 2).
4. Classify honestly with the status enum. 'patched-verified' REQUIRES that you ran the old repro and it no longer reproduces. If you could not run it, that is 'patched-code-only' — do not inflate.
5. Judge FIX QUALITY: is the new behavior PINNED by a theorem (would reverting the fix turn the build red?) or is it an unpinned impl patch? An unpinned fix is a coverage-gap: it can silently regress. Say so in fixQuality.
6. If a fix INTRODUCED a new problem, or you trip over a new bug, record it in newCandidates. Upstream added big new surface (TCP, EDNS0, QNAME-minimisation, egress filter) — new code, new bugs.
${canBuild
  ? `YOU MAY BUILD. You own the build tree for this step. Apply revert/mutation edits, 'lake build', read the signal, then MANDATORY per-file cleanup (rule 1 + 7): 'git checkout -- <only the exact files you edited>', 'lake build', '${REPO}/review/env/restart-verid.sh', and confirm 'git status' shows tracked source clean. Apply rule 4 (semantic vs brittle) rigorously — that distinction is the whole point.`
  : `DO NOT RUN 'lake build' and do NOT edit tracked source — another stage owns the build tree (rule 6). Query the RUNNING rig. If an item can only be settled by a build, mark it 'inconclusive' and say why; the provenance batch will pick it up.`}
${RIG}
${RULES}
Return one REGRESSION_ITEM per finding in your batch, each with real command output in 'evidence'. Where a finding is confirmed STILL-PRESENT, write/refresh ${REPO}/review/findings/NNN-*.md and say so in 'reason'. Do not pad: a short honest 'inconclusive' beats a confident guess.`,
    { label: `regress:${b.id}`, phase: 'Regression', model: 'fable', schema: REGRESSION })
  if (r) {
    regressionResults.push({ batch: b.id, ...r })
    const tally = (r.items || []).reduce((a, i) => { a[i.status] = (a[i.status] || 0) + 1; return a }, {})
    log(`regress ${b.id}: ${(r.items || []).length} items — ${JSON.stringify(tally)}`)
  } else {
    log(`regress ${b.id}: NO RESULT after retries (transient API) — treat as inconclusive`)
  }
}

const regItems = regressionResults.flatMap(r => r.items || [])
const stillPresent = regItems.filter(i => ['still-present', 'partially-fixed', 'regressed-new-bug', 'scoped-out-disputed'].includes(i.status))
const patched = regItems.filter(i => i.status.startsWith('patched'))
log(`REGRESSION SUMMARY: ${regItems.length} findings re-tested — ${patched.length} patched, ${stillPresent.length} still live/disputed`)

// =============================================================================
// PHASE 2 — ITERATIVE HUNT for NEW bugs
// =============================================================================
const key = c => `${c.kind}|${c.location}|${c.title}`.toLowerCase().replace(/\s+/g, ' ').trim()
const seen = new Set()
const confirmed = []
const mutantLog = []
const allCandidates = []
let dryRounds = 0

const kb = [
  `PREFLIGHT: build ok. ${(build.details || '').slice(0, 200)}`,
  `PREFLIGHT: axiom audit ${axioms?.ok ? 'CLEAN' : 'NOT CLEAN — treat every proof-based claim with suspicion'}: ${(axioms?.summary || '').slice(0, 250)}`,
  `PREFLIGHT: FRESH execution-path map at review/pathmap.md — consult before mutating anything. ${(pathmap?.summary || '').slice(0, 250)}`,
  `REGRESSION: ${patched.length}/${regItems.length} prior findings verified patched; ${stillPresent.length} still live.`,
  ...regItems.map(i => `REGRESSION ${i.finding}: ${i.status} — ${(i.reason || '').slice(0, 140)}${i.fixQuality ? ` [fix quality: ${(i.fixQuality || '').slice(0, 120)}]` : ''}`),
]

// Carry regression-discovered candidates into round 1 rather than re-deriving them.
const carried = regressionResults.flatMap(r => r.newCandidates || [])
for (const c of carried) { const k = key(c); if (!seen.has(k)) { seen.add(k); allCandidates.push(c) } }
if (carried.length) log(`Carrying ${carried.length} new candidates from the regression phase into round 1`)

const kbSummary = () => `KNOWLEDGE BASE (accumulated; build on it, do not re-litigate settled items):
${kb.map(s => '- ' + s).join('\n')}
MUTANTS ALREADY TRIED: ${mutantLog.length ? mutantLog.map(m => `${m.id}=${m.classification}(${m.reason})`).join(' | ') : 'none yet'}`

// What makes THIS hunt different from the prior review's.
const NEWSURFACE = `WHERE THE NEW BUGS ARE. The prior review exhausted the OLD tree's easy finding space; do not just re-walk it. Upstream 26b5849 is a huge commit that ADDED, since the last review:
- DNS-over-TCP: VeriDNS/Impl/TcpFraming.lean, Proof/TcpFraming.lean, Proof/ServeTcp.lean, Proof/ServeSequence.lean. 2-byte length prefix framing is a classic bug farm: short/split/coalesced writes, a length prefix that disagrees with the message, zero-length frames, slow-loris, connection reuse/pipelining, TCP-vs-UDP behavioral divergence, the TC=1 -> TCP-retry path.
- EDNS0: VeriDNS/Impl/Edns.lean, Resolver.lean ~:486 emits an OPT RR with Edns.advertisedUdpSize. OPT-record edge cases: multiple OPTs, OPT in the wrong section, a bogus/tiny advertised size, unknown EDNS version (must be BADVERS per RFC 6891), flags/DO bit, OPT in the QUERY being echoed.
- QNAME-minimisation: DomainName.minimisedName, Resolver.lean ~:459 (RFC 9156). Classic failures: minimisation breaking on empty non-terminals, CNAME-at-a-parent, the loop not terminating, leaking the full name anyway, or an off-by-one in the label count.
- The egress filter: Server.lean:336 doNotQueryNets + blockedEgress, with a VERI_DNS_ALLOW_LOOPBACK_EGRESS env bypass. Check the ACL arithmetic itself (AclEntry.matches — off-by-one in the prefix mask?), whether IPv6 is covered at all, and whether the filter is applied on EVERY egress path or only some.
- New capstones: Proof/ResolveWithIOSound.lean, ServeSound.lean, ServeAdequacy.lean, SpineAdequacy.lean, NameTreeComplete.lean, SentMinimised.lean. These are ADEQUACY/COMPLETENESS claims — a NEW kind of claim the prior review never audited. Adequacy theorems are exactly where an over-premised or vacuous statement hides ("the server delivers treeResolve's verdict whole" — under what hypotheses? are they dischargeable at the real entry point? is it ever APPLIED?).
Also: the remediation commit itself is new code. A fix written fast to close a review finding is a prime bug site — especially the scrub rewrite (reachableNamesB/setOwnerB owner-rewriting) and the sbelt fallback in stepFindServers.`

for (let round = 1; round <= MAX_ROUNDS; round++) {
  phase('Find')
  log(`=== Round ${round}/${MAX_ROUNDS} ===`)
  const KB = kbSummary()
  const dedupeHint = allCandidates.length
    ? `Do NOT re-raise these (find NEW/deeper):\n${allCandidates.map(c => `- [${c.kind}] ${c.title} @ ${c.location}`).join('\n')}`
    : 'No prior candidates.'

  const found = (await parallel([
    () => agentR(
`DEDICATED reading-source agent auditing VeriDNS at ${REPO} (round ${round}), branch review/bug-hunt-2 @ upstream 26b5849. Read three things AGAINST each other: the RFCs (${REPO}/rfc/ — note 3597, 8020, 9156 are NEW), the mature reference implementation unbound (${REPO}/unbound/, C source), and the VeriDNS Lean sources (${REPO}/VeriDNS/Impl, ${REPO}/VeriDNS/Spec).
Find DISCREPANCIES: something unbound does (a defense, check, normalization, edge case) that VeriDNS omits or does differently, in a way that would be OBSERVABLE and WRONG. Read ${REPO}/review/pathmap.md FIRST and focus ON-PATH code.
${NEWSURFACE}
Also worth reading: ${REPO}/docs/remediation-plan.md — it documents what upstream changed and WHY, including things they consciously scoped out. A scoped-out decision defended by a stale rationale is a finding.
Cite the unbound file:line and/or RFC section AND the VeriDNS location, and give a concrete runtime experiment.
${RULES}
${KB}
${dedupeHint}
Do NOT edit code. Return candidates (kind 'discrepancy'/'scope-gap'); a few well-substantiated leads beat many shallow ones.`,
      { label: `R:read r${round}`, phase: 'Find', model: 'fable', schema: CANDIDATES }),

    () => agentR(
`Spec-auditor for VeriDNS (round ${round}) at ${REPO}. Hunt WEAK, VACUOUS, or OVER-PREMISED theorems — specs loose enough that an observably-wrong implementation still satisfies them. Read ${REPO}/review/pathmap.md first.
${NEWSURFACE}
PRIORITISE THE NEW CAPSTONES (ResolveWithIOSound, ServeSound, ServeAdequacy, SpineAdequacy, NameTreeComplete, SentMinimised, ServeTcp). The prior review audited the SOUNDNESS capstones and found them genuine; these ADEQUACY/COMPLETENESS ones are unaudited. Upstream's own docs (docs/liveness-plan.md, docs/total-simulation-plan.md, docs/assurance-roadmap.md) describe the intent — check the delivered theorem against the advertised intent.
Beware the classic dodges: (a) a "law" that is a TAUTOLOGY because the thing it constrains is DEFINED as that law; (b) an obligation quantified over a domain that excludes the interesting case; (c) a theorem with so many hypotheses it cannot apply to a real client query — check whether its hypotheses are dischargeable at the real entry point, and whether the theorem is ever APPLIED at all (a terminal orphan is deadweight — old finding 025); (d) an "oracle" premise that assumes the conclusion (what is ASSUMED vs PROVEN at M=IO — see NetworkConsistent and ${REPO}/review/evidence/oracle-analysis.md).
Techniques: write SPOTs under ${REPO}/review/evidence/spots/ — a SENSIBLE property that SHOULD be provable, and a NONSENSE property that should NOT be (if it proves, that is vacuity). ${REPO}/review/evidence/spots/ already has ~22 from the prior review — read them for technique, and check whether the ones that exposed weaknesses still do. You MAY run 'lake env lean <file>' on SPOTs. Do NOT run 'lake build' and do NOT edit tracked Impl/Proof files.
${RULES}
${KB}
${dedupeHint}
Return candidates (kind 'weak-theorem'); each MUST name a concrete weaponizable mutant in howToVerify AND say how to distinguish a real semantic catch from proof-script brittleness.`,
      { label: `S:spec r${round}`, phase: 'Find', model: 'fable', schema: CANDIDATES }),

    () => agentR(
`Dynamic differential + penetration-testing agent for VeriDNS (round ${round}) at ${REPO}. Produce OBSERVED behavior, never speculation.
${RIG}
Do NOT rebuild veri-dns (the weaponize stage owns the build tree); query the running rig.
${NEWSURFACE}
1. DIFFERENTIAL: a broad spread against BOTH resolvers — A/AAAA/CNAME/MX/SOA/NS/TXT/DS/SRV/PTR, NXDOMAIN, empty non-terminals, long and mixed-case names, CNAME chains, malformed/compression-pointer packets, meta QTYPEs, odd opcodes, EDNS0 (with/without OPT, bogus versions, tiny advertised sizes), and **TCP (+tcp) for everything you test over UDP** — a UDP/TCP divergence is a finding in itself. Diff RCODE, answer set, TTLs, flags, and the authority/additional sections.
2. PENTEST: cache poisoning — off-path spoofed responses racing the real one (${REPO}/review/env/spoof.py), out-of-bailiwick glue/answer/additional injection, unrelated records piggybacked on answers, TTL abuse, id/question mismatch, rogue-ancestor answers, lame/uncooperative servers, TCP framing abuse (bad length prefix, split writes, zero-length frames, slow-loris, pipelining), and QNAME-minimisation edge cases (empty non-terminals, CNAME at a parent).
3. Cross-reference divergences to RFC sections and to what pathmap.md says the code claims to defend.
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
${NEWSURFACE}
HIGH-VALUE TARGET CLASSES FOR THIS RUN:
- The NEW code, which no prior mutation has probed: TCP framing (TcpFraming.lean), EDNS0 (Edns.lean), QNAME-minimisation (minimisedName), the egress ACL (doNotQueryNets/AclEntry.matches).
- THE REMEDIATION FIXES THEMSELVES. Revert each fix and see if ANY theorem goes red: reachableNamesB (004), the nameEqCI owner check in extractCname (036), scrubAuthorityB (013), blockedEgress (021), the sbelt fallback in stepFindServers (015). A fix that no theorem pins is an unpinned fix that can silently regress — that is a reportable coverage-gap, and it is the sharpest question this review can ask of the remediation.
- The new adequacy capstones: can you make the server deliver an INCOMPLETE answer while ServeAdequacy/NameTreeComplete stay green?
- Still-live findings from the regression phase: ${stillPresent.length ? JSON.stringify(stillPresent.map(i => ({ f: i.finding, why: (i.reason || '').slice(0, 120) }))) : 'none'}
${kbSummary()}
CRUCIAL — learn from prior verdicts: if a mutation came back 'proof-caught-brittle' (only a tactic broke; the statement stayed true), design a REFINED version that routes around the incidental catch and note that a minimal proof-script repair is warranted. Do NOT repeat anything already 'proof-caught-semantic' — that is settled.
${RULES}
Return 2-5 mutants; fill 'distinguish' for each.`,
    { label: `synth r${round}`, phase: 'Synthesize', model: 'fable', schema: MUTANTS })
  const mutants = (synth?.mutants || []).filter(m => !mutantLog.some(x => x.id === m.id))
  log(`Round ${round}: synthesized ${mutants.length} mutants`)

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
3. If BROKE: decide SEMANTIC (a theorem STATEMENT became false -> verification is load-bearing here) vs BRITTLE (only a tactic failed; statement still true). If brittle, attempt a MINIMAL local proof-script repair and rebuild — if it then goes green, continue to step 4; that is the real test (rule 4).
4. If GREEN (with or without a minimal repair): 'lake build veri-dns', then '${REPO}/review/env/restart-verid.sh' to load the mutant, then reproduce the wrong behavior from the attacker ns. RESTART BOTH RESOLVERS FIRST (rule 3) and compare veri-dns@${NET}.2:5300 vs unbound@${NET}.3:5301. Capture dig/tcpdump output. Set unboundDiffers honestly (rule 2).
5. Classify per the schema.
6. If it is a real finding (bad-spec / coverage-gap / impl-bug AND unboundDiffers), write ${REPO}/review/findings/NNN-<slug>.md (next free 3-digit NNN — the prior review used up to 048, so start at 049) with: the claim, the mutation diff, the build result proving proofs stayed green, the reproduction commands+output, and an RFC/unbound citation for why it is wrong.
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
If confirmed, write ${REPO}/review/findings/NNN-<slug>.md (next free NNN; start at 049 — the prior review used up to 048) with the setup, reproduction commands+output, and an RFC/unbound citation. If you staged any responder/config in the rig, restore the baseline afterward.
${RULES}
Return the verdict with a one-line 'reason'.`,
      { label: `verify:${c.location}`, phase: 'Verify', model: 'fable', schema: VERDICT })
    if (v) {
      kb.push(`VERIFY ${v.title}: ${v.classification} — ${(v.reason || '').slice(0, 160)}`)
      if (['bad-spec', 'coverage-gap', 'impl-bug'].includes(v.classification) && v.unboundDiffers !== false) confirmed.push(v)
      log(`verify ${v.title} -> ${v.classification} (unboundDiffers=${v.unboundDiffers})`)
    }
  }

  // GENUINE dry detection: an API error is NOT "no findings" (HARNESS §5.6)
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
// PHASE 3 — REPORT
// =============================================================================
phase('Report')
const report = await agentR(
`You are the report-synthesis agent for the VeriDNS security & verification review at ${REPO}. Write ${REPO}/review/REPORT.md — the canonical deliverable, REPLACING the old one (which describes commit 8e4e16d and is now stale). Preserve the old report's honest structure and its refuted-candidates section, but this is a NEW report against upstream 26b5849.
THIS REPORT HAS TWO QUESTIONS TO ANSWER, and the first is new:
(A) **Did the remediation actually work?** Upstream shipped one large commit (26b5849) with ${REPO}/docs/remediation-plan.md claiming "every review finding is now fixed, theorem-pinned, or scoped out with rationale." We re-tested finding by finding. Report the SCORECARD honestly: what is genuinely fixed (old repro no longer reproduces on the rig), what is fixed in code but unverified, what is STILL PRESENT, what was scoped out and whether that scoping is defensible. Where a fix is real, SAY SO plainly — a review that only reports bad news is not trustworthy either. Also report FIX QUALITY: a fix no theorem pins can silently regress, which is itself a finding.
(B) **Is the verification load-bearing** — does the proof rule out bugs, or is correctness inherited from mirroring unbound? Same question the prior review asked, now against much more code (TCP, EDNS0, QNAME-minimisation, and new adequacy/completeness capstones the prior review never audited).
Inputs to read and synthesize:
- ${REPO}/review/findings/ — every finding file, old and new (agent-assigned numbers COLLIDE; your report is the canonical index, so disambiguate).
- ${REPO}/review/pathmap.md — the FRESH on-path vs off-path classification.
- ${REPO}/review/HARNESS.md — method and its constraints.
- ${REPO}/docs/remediation-plan.md — what upstream claims it fixed.
- The prior report is in git: 'git show review/bug-hunt:review/REPORT.md' — for continuity and the refuted list.
- Preflight: build ${JSON.stringify((build.summary || '').slice(0, 300))}; axiom audit ${JSON.stringify((axioms?.summary || '').slice(0, 300))}.
- FULL REGRESSION RESULTS:
${JSON.stringify(regItems, null, 1).slice(0, 12000)}
- Accumulated knowledge base and verdicts:
${kbSummary()}
Required sections:
1. **Bottom line / trust verdict.** Decisive and honest. Lead with the remediation scorecard (A), then the load-bearing verdict (B). State plainly what a reader may and may not infer.
2. **Remediation scorecard** — a table: finding | prior severity | upstream claim | our verdict | evidence. This is the section the reader most wants.
3. **Findings still live + NEW findings**, grouped by severity/class, each with: what it is, the trigger, a link to the reproduction, and an RFC/unbound citation. For every bad-spec, state the injected mutation that slipped through the proofs.
4. **Refuted candidates** — with why (unbound did the same => trust model, not a bug). Evidence of rigor; do not hide it.
5. **Verification architecture** — which verified code the running server actually executes; flag off-path/decorative verification. Cover the NEW capstones explicitly.
6. **Navigation guide** — a prioritized reading list for a human reviewer.
7. **Method + caveats** — the rig renumbering (203.0.113.0/24, forced by upstream's new egress filter) and why; any coverage gaps, unevaluated mutations, rounds degraded by API errors, findings not isolation-verified.
Distinguish clearly between claims verified by an ISOLATED differential re-run and claims resting on a single agent's observation. Do not overstate: a green-building mutant proves a SPEC gap; it is a BUG only if reachable at runtime.
Report ok=true with a one-paragraph summary of the verdict you wrote.`,
  { label: 'report:synthesis', phase: 'Report', model: 'fable', schema: PREFLIGHT })
log(`Report: ok=${report?.ok} — ${report?.summary || 'no result'}`)

log(`Regression + hunt complete. prior findings re-tested: ${regItems.length} (${patched.length} patched, ${stillPresent.length} live). NEW confirmed findings: ${confirmed.length}`)
return {
  preflight: { build, axioms, pathmap, env },
  regression: { items: regItems, patched: patched.length, stillPresent: stillPresent.length, byStatus: regItems.reduce((a, i) => { a[i.status] = (a[i.status] || 0) + 1; return a }, {}) },
  confirmed,
  mutantLog,
  byClass: confirmed.reduce((a, v) => { a[v.classification] = (a[v.classification] || 0) + 1; return a }, {}),
  knowledgeBase: kb,
  report,
}
