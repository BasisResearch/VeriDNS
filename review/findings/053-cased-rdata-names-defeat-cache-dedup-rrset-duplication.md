# 053 — Client-inducible unbounded RRset duplication: 0x20-cased RDATA names defeat case-sensitive cache dedup

- **Location:** `VeriDNS/Impl/Cache.lean:71-74` (`DnsCache.store` dedup predicate)
- **Verdict:** CONFIRMED (unbound disagrees on the identical path/data with cold caches)
- **Class:** proof-caught-semantic / spec gap — reachable at runtime, client-inducible

## Mechanism

`DnsCache.store` dedupes cached RRs with a byte-exact comparison of `rdata`:

```lean
let records := c.records.filter fun e =>
  !(nameEqCI e.rr.name rr.name && e.rr.type == rr.type && e.rr.class == rr.class
    && (e.expiry != expiry || e.rr.rdata == rr.rdata))
```

An existing entry `e` is dropped only when name(CI)/type/class match **and**
(`e.expiry != expiry` **or** `e.rr.rdata == rr.rdata`). For two records with the
same owner/type/class, the **same** expiry (same-second refetch of a fixed-TTL
record), and rdata that differs **only in the case of a DNS name embedded in the
RDATA**, both disjuncts are false, so the removal predicate is `false`: the old
entry is kept and the new one pushed — a duplicate RR in the RRset.

Two ingredients make the RDATA case vary on every fetch:

1. **0x20 query-case randomization.** `VeriDNS/Impl/Server.lean:39` rewrites the
   outgoing qname with `DomainName.randomizeCase cid qu.qname`, so each upstream
   fetch carries a fresh random casing of `example.test`.
2. **Name compression in the SOA RDATA.** The authoritative SOA's MNAME/RNAME
   (`ns.example.test`, `hostmaster.example.test`) are compressed as pointers back
   to the question's `example.test`. When veri-dns decompresses, the pointed-to
   suffix inherits the randomized case, so the stored RDATA bytes differ on every
   refetch (`ns.ExaMPLe.TeST.`, `ns.exaMplE.TESt.`, ...).

`ANY` (qtype=255) is never answered from cache, so an ordinary client (no
spoofing) can force a fresh cased upstream fetch on every query, growing the
cached SOA RRset without bound. RFC 2181 §5 requires an RRset to contain no
duplicate RRs, and DNS names compare case-insensitively — so all these records
are duplicates. Result: cache-memory bloat + response-size amplification (a
1-record RRset becomes N attacker-chosen records, delivered in full over TCP).

## Reproduction (rig, both resolvers restarted cold first)

```
$ ssh 'systemctl restart veridns-verid veridns-ref; sleep 2;
       ip netns exec attacker dig @203.0.113.2 -p 5300 example.test SOA +noall +answer'
example.test.  3600  IN  SOA  ns.ExaMPLe.TeST. hostmaster.ExaMPLe.TeST. 1 3600 900 604800 3600

$ ssh 'ip netns exec attacker dig @203.0.113.3 -p 5301 example.test SOA +noall +answer'
example.test.  3600  IN  SOA  ns.example.test. hostmaster.example.test. 1 3600 900 604800 3600
```

veri-dns already serves the SOA RDATA with 0x20-randomized case; unbound
normalizes to lowercase.

Abuse sequence — one prime, then 12 `ANY` queries, then read the SOA RRset:

```
=== veri-dns SOA after 12 ANY ===   (over TCP, +noall +answer)
example.test.  3600  IN  SOA  ns.exaMplE.TESt. hostmaster.exaMplE.TESt. 1 ...
example.test.  3600  IN  SOA  ns.EXAMpLE.TeSt. hostmaster.EXAMpLE.TeSt. 1 ...
example.test.  3600  IN  SOA  ns.ExaMple.tesT. hostmaster.ExaMple.tesT. 1 ...
example.test.  3600  IN  SOA  ns.ExamPLe.teST. hostmaster.ExamPLe.teST. 1 ...
example.test.  3600  IN  SOA  ns.eXAMPLe.tEST. hostmaster.eXAMPLe.tEST. 1 ...
example.test.  3600  IN  SOA  ns.ExampLE.test. hostmaster.ExampLE.test. 1 ...
example.test.  3600  IN  SOA  ns.ExAMPLe.tEst. hostmaster.ExAMPLe.tEst. 1 ...
example.test.  3600  IN  SOA  ns.eXAMpLe.TEST. hostmaster.eXAMpLe.TEST. 1 ...
example.test.  3600  IN  SOA  ns.ExAMPLe.TESt. hostmaster.ExAMPLe.TESt. 1 ...
example.test.  3600  IN  SOA  ns.EXaMPle.tEST. hostmaster.EXaMPle.tEST. 1 ...
example.test.  3600  IN  SOA  ns.ExampLe.teSt. hostmaster.ExampLe.teSt. 1 ...
example.test.  3600  IN  SOA  ns.ExAmpLe.tEst. hostmaster.ExAmpLe.tEst. 1 ...
  -> 12 identical SOAs, differing only in 0x20 case

=== unbound SOA after 12 ANY ===
example.test.  3589  IN  SOA  ns.example.test. hostmaster.example.test. 1 ...
  -> exactly 1
```

## Mechanism control

Priming an **A** record (RDATA = raw IPv4 address, no embedded name, so unaffected
by 0x20) and running the same 12 ANY queries:

```
veri-dns A RRset:   1     <- unaffected (rdata has no name)
veri-dns SOA RRset: 11    <- grew (rdata carries cased MNAME/RNAME)
```

This isolates the mechanism to case-variant DNS names inside RDATA defeating the
byte-exact `e.rr.rdata == rr.rdata` comparison.

## Oracle disagreement (rule 2)

unbound (`@203.0.113.3:5301`), on the identical query path against the identical
authoritative data with a cold cache, holds the SOA RRset at exactly **1** under
the same abuse sequence. It canonicalizes RDATA names to a single case and
correctly treats the refetches as the same record. veri-dns grows the RRset
monotonically (2,3,...,12). This is a VeriDNS-specific defect, not the DNS trust
model.

## Why no theorem catches it

Every verdict/total capstone carries `hqany: qu.qtype != 255`, so the ANY path
(the amplification knob) is excluded from the guarantees. `DnsCache.store`'s
dedup filter and `RRsetComplete.cacheRRsNorm_complete` only promise to *keep
every survivor* — which is exactly the wrong property here, since each
case-variant duplicate counts as a distinct survivor. RDATA-embedded names are
never canonicalized before the byte comparison.

## RFC citation

RFC 2181 §5: "the RRs [...] within an RRSet [...] are described as being
identical. [...] DNS names [...] are compared in a case insensitive manner." An
RRSet must not contain duplicate RRs; two SOA records differing only in the case
of their MNAME/RNAME are duplicates.

## Cleanup

No source files were edited (this is a runtime differential, not a mutation).
Both resolvers were restarted cold before the differential. `git status` shows no
tracked `VeriDNS/` source changes from this run.
