# VeriDNS security-review test environment

A self-contained, controlled DNS hierarchy plus two recursive resolvers for
differential testing and cache-poisoning / spoofing experiments. Everything
runs **inside one throwaway test VM** (the `penn-testing` mkosi/qemu VM), using
Linux **network namespaces** wired to a bridge. No public DNS is ever touched.

- **Resolver under test:** `veri-dns` (the Lean binary), UDP **5300**.
- **Reference resolver:** `unbound`, UDP **5301**.
- **Fake hierarchy:** `nsd` serving a fake root `.` -> TLD `test.` -> leaf
  `example.test.`, one authoritative server per level.
- **Attacker vantage:** a namespace that can `dig` both resolvers and inject
  spoofed UDP packets at them.

Why a VM: the host `sudo` needs a password (no non-interactive root), and
`unbound`/`nsd` are not installed on the host. Inside the VM we are genuinely
root and can `pacman -S` them and create namespaces freely. The VM uses ~2 GiB
RAM (well under the 12 GiB ceiling).

---

## 1. Layout (namespaces, IPs, ports)

All nodes sit on bridge **`brdns` = 10.53.0.1/24** in the VM's root netns.

| namespace  | address(es)                              | runs                                   | port |
|------------|------------------------------------------|----------------------------------------|------|
| `auth`     | 10.53.0.10 (root), 10.53.0.11 (tld), 10.53.0.12 (leaf) | 3x `nsd` (root/tld/leaf zones) | 53 |
| `auth`     | 198.41.0.4, 199.9.14.201, 192.33.14.30, 199.7.91.13, 192.203.230.10 | fake-root `nsd` also binds these | 53 |
| `verid`    | 10.53.0.2                                | **veri-dns** (resolver under test)     | **5300** |
| `unbound`  | 10.53.0.3                                | **unbound** (reference resolver)       | **5301** |
| `attacker` | 10.53.0.99                               | `dig`, `spoof.py`, `tcpdump`           | -    |

**The five 198.x/199.x/192.x addresses are the real root-server IPs that
`veri-dns` has hardcoded in `VeriDNS/Main.lean`.** We cannot change the resolver
(no source edits), so instead the fake root `nsd` binds those exact IPs, and
`verid`/`unbound`/`attacker` get `/32` on-link routes to them. veri-dns's
hardcoded root queries therefore land on our fake root. unbound is pointed at
the same root via `unbound/root.hints`.

The zones (`review/env/nsd/zones/`):

```
.               NS a-e.root-servers.net (198.41.0.4 ...)   delegates: test.
test.           NS a.tld.test (10.53.0.11)                 delegates: example.test.
example.test.   NS ns.example.test (10.53.0.12)
                @    A     10.53.0.100
                host A     10.53.0.101
                www  CNAME example.test.
                alias CNAME host.example.test.
```

---

## 2. Bring it up from scratch

### 2a. Boot the VM (leave it running in its own terminal)

```sh
cd /home/yiyun/Experiments/VeriDNS/penn-testing
make vm            # takes over the terminal; boots in ~20 s. `poweroff` to stop.
```

The repo's `penn-testing/` tree is bind-mounted read-write at `/root/dev`
inside the VM; the bring-up stages files there.

### 2b. Build the rig (from any other terminal)

```sh
/home/yiyun/Experiments/VeriDNS/review/env/up.sh
```

`up.sh` (host side) does everything, idempotently:
1. checks the VM is reachable over vsock (`penn-testing/vm/ssh.sh`);
2. stages the configs + zones + the freshly built `veri-dns` binary + `spoof.py`
   into `penn-testing/_vmdns/` (visible as `/root/dev/_vmdns/` in the VM);
3. ensures the VM has `unbound`, `nsd`, `dig` (sets a pacman mirror + resolv.conf,
   disables signature checking on this throwaway VM, `pacman -S` if missing);
4. runs `vm-up.sh` inside the VM, which builds the bridge + 4 namespaces and
   starts the 5 daemons as **transient systemd units** (`veridns-*.service`)
   so they survive the ssh session that launched them.

Expected tail: five `veridns-*.service ... active running` lines and `>> done.`

> If the VM was rebuilt/rebooted, `up.sh` reinstalls packages automatically —
> just re-run it. Nothing on the host needs root.

---

## 3. Query each resolver

Helper (`query.sh`) digs from the `attacker` namespace:

```sh
review/env/query.sh verid   host.example.test A     # veri-dns  @10.53.0.2:5300
review/env/query.sh unbound host.example.test A     # unbound   @10.53.0.3:5301
```

Or raw, over the VM shell:

```sh
cd penn-testing
./vm/ssh.sh 'ip netns exec attacker dig @10.53.0.2 -p 5300 host.example.test A'
./vm/ssh.sh 'ip netns exec attacker dig @10.53.0.3 -p 5301 host.example.test A'
```

**Verified agreement** (captured in `review/env/VERIFICATION.txt`): both
resolvers return `host.example.test A 10.53.0.101`, `example.test A
10.53.0.100`, and `www.example.test CNAME example.test A 10.53.0.100`.

---

## 4. Restart just veri-dns after a rebuild

After `lake build` produces a new binary, re-stage it and restart only the
resolver-under-test unit (the fake hierarchy and unbound keep running):

```sh
review/env/restart-verid.sh
```

(It stops `veridns-verid`, replaces `/opt/dnsenv/veri-dns` — you cannot `cp`
over a running binary, hence stop-first — restarts the unit, and prints a test
answer.)

Manual equivalent (the repo root is NOT mounted in the VM, so stage via
`penn-testing/_vmdns/`, which appears as `/root/dev/_vmdns/` in the guest):

```sh
# host:
cp -a .lake/build/bin/veri-dns penn-testing/_vmdns/veri-dns
# VM:
./vm/ssh.sh 'systemctl stop veridns-verid; rm -f /opt/dnsenv/veri-dns;
             cp -a /root/dev/_vmdns/veri-dns /opt/dnsenv/veri-dns;
             systemd-run --unit=veridns-verid --collect \
               ip netns exec verid /opt/dnsenv/veri-dns'
```

---

## 5. Spoof / inject from the attacker vantage

`spoof.py` (in the `attacker` ns) forges a UDP DNS **response** with an
arbitrary source IP aimed at a resolver — off-path response spoofing to test
txid/source-port matching and bailiwick checks.

```sh
cd penn-testing
# forge a poisoned answer for host.example.test, pretending to be the leaf NS,
# aimed at unbound:
./vm/ssh.sh 'ip netns exec attacker python3 /opt/dnsenv/spoof.py \
    --dst-ip 10.53.0.3 --dst-port 5301 --src-ip 10.53.0.12 \
    --qname host.example.test --answer-ip 6.6.6.6 --txid 0xbeef'

# aim it at veri-dns instead:
./vm/ssh.sh 'ip netns exec attacker python3 /opt/dnsenv/spoof.py \
    --dst-ip 10.53.0.2 --dst-port 5300 --src-ip 10.53.0.12 \
    --qname host.example.test --answer-ip 6.6.6.6 --txid 0x1234'
```

Watch it land / watch resolver traffic with tcpdump:

```sh
./vm/ssh.sh 'ip netns exec unbound tcpdump -n -i v-unbound udp and port 5301'
./vm/ssh.sh 'ip netns exec verid   tcpdump -n -i v-verid'
```

Verified: the spoofed packet (`10.53.0.12.53 > 10.53.0.3.5301 ... A 6.6.6.6`)
reaches unbound and is correctly ignored (no matching outstanding query). To
build a real poisoning race, run a legit query for a not-yet-cached name in one
loop and flood `spoof.py` with guessed txids in another; a correct resolver
never caches the forgery.

Logs live in the VM under `/run/veridns-*.log` (per unit) and via
`./vm/ssh.sh 'journalctl -u veridns-ref'` etc.

---

## 6. Teardown

```sh
review/env/down.sh              # stops the 5 units + removes namespaces/bridge
                                # (VM keeps running)
```

Stop the VM entirely: type `poweroff` in the `make vm` terminal (its boot is a
throwaway copy, so all in-guest state — packages, namespaces — vanishes; re-run
`up.sh` after the next `make vm` to rebuild everything).

---

## 7. Design notes & caveats

- **One nsd per hierarchy level.** A single nsd serving all three zones on all
  IPs would answer grandchild names *authoritatively* from the root IP; a
  correct resolver (unbound) rejects that as out-of-bailiwick and returns
  NXDOMAIN. Splitting into root/tld/leaf servers (each serving only its zone)
  makes them emit proper referrals. veri-dns happens to accept the merged form,
  which is itself a notable behavioural difference worth reviewing.
- **`.test` is an RFC 6761 special-use TLD.** unbound ships a built-in
  `local-zone: "test."` that returns an immediate authoritative NXDOMAIN and
  never queries upstream. `unbound.conf` disables it with
  `local-zone: "test." nodefault`. veri-dns has no such special-casing.
- **DNSSEC is off** (unbound `module-config: "iterator"`): the fake hierarchy is
  unsigned, so there is no trust anchor. Cache-poisoning tests here exercise the
  classic txid/port/bailiwick defences, not DNSSEC validation.
- **RFC1918 answers:** the leaf serves `10.53.0.x` A records; unbound's rebind
  protection would strip them, so `private-domain: "test."` permits them.
- **The repo root is NOT bind-mounted in the VM** — only `penn-testing/` is
  (as `/root/dev`). That is why `up.sh` copies the `veri-dns` binary into
  `penn-testing/_vmdns/` rather than referencing `.lake/` directly.
- **Throwaway VM.** Packages installed by `up.sh` and all namespaces are lost on
  `poweroff`. `up.sh` is fully idempotent and re-installs/rebuilds on demand.
- **Signature checking is disabled** in the guest's `pacman.conf` (the image
  ships no initialized keyring). Acceptable for a local-only throwaway test VM.

---

## 8. Troubleshooting

- **`up.sh`: "VM not reachable"** — boot it first: `cd penn-testing && make vm`,
  and keep it running in that terminal. `make vm` and the ssh must share the
  same login session (both are fine from this shell).
- **`RTNETLINK answers: File exists` during bring-up** — a stale `veridns-*`
  unit from a previous run is holding a namespace/veth. `down.sh` now stops
  *all* `veridns-*` units; re-run `down.sh` then `up.sh`.
- **`dig ... connection refused`** — the daemons died with their launching
  session. They are started as `systemd-run` transient units precisely to avoid
  this; check `./vm/ssh.sh 'systemctl list-units veridns\*'` and
  `journalctl -u veridns-ref`.
- **unbound returns NXDOMAIN for `*.test`** — the `local-zone: "test."
  nodefault` line is missing from `unbound.conf`.
- **veri-dns can't reach the root** — confirm the `/32` routes to the root IPs
  exist: `./vm/ssh.sh 'ip netns exec verid ip route'` should list
  `198.41.0.4/32 dev v-verid` etc.

---

## 9. File manifest (`review/env/`)

| file | side | purpose |
|------|------|---------|
| `up.sh`            | host | one-command bring-up (stage + provision + start) |
| `down.sh`          | host | teardown inside the VM |
| `query.sh`         | host | `dig` a resolver from the attacker ns |
| `restart-verid.sh` | host | re-stage + restart only veri-dns after a rebuild |
| `vm-up.sh`         | VM   | build bridge/namespaces, start the 5 units |
| `vm-down.sh`       | VM   | stop units, delete namespaces/bridge |
| `spoof.py`         | VM   | off-path spoofed-DNS-response injector |
| `nsd/nsd-root.conf`, `nsd-tld.conf`, `nsd-leaf.conf` | VM | the three authoritative servers |
| `nsd/zones/*.zone` | VM | root / test. / example.test. zone data |
| `unbound/unbound.conf`, `unbound/root.hints` | VM | reference resolver config |
| `VERIFICATION.txt` | -    | captured proof both resolvers answer & agree |
| `vm-console.log`   | -    | VM boot console capture |
```
