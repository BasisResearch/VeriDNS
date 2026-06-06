# veri-dns

A DNS resolver verified against the RFC specifications in Lean 4.

## Idea

We implement a DNS resolver and formally verify it against the RFC
documents themselves. The `include_rfc` macro embeds RFC text verbatim
into Lean source files and checks it at compile time against the
actual RFC documents. Custom parsers and de-elaborators will eventually
translate this natural language into formal theorems.

## Roadmap

### Phase 1: Infrastructure (current)
- [x] Lake project setup
- [x] `include_rfc[num][from:to] { ... }` compile-time macro
- [x] RFC text extraction with page break stripping

### Phase 2: Formal Specs
- [ ] Message format (RFC 1035 section 4.1)
- [x] Header fields (RFC 1035 section 4.1.1)
- [x] Question section (RFC 1035 section 4.1.2)
- [x] Resource record format (RFC 1035 section 4.1.3)
- [x] Message compression (RFC 1035 section 4.1.4)
- [x] Domain name encoding (RFC 1035 section 3.1)
- [ ] RR types and classes (RFC 1035 sections 3.2-3.4)
- [ ] Transport: UDP/TCP (RFC 1035 section 4.2)

While doing this, we should endeavor to build reusable components with:
- Custom syntax/parsers for RFC spec language
- De-elaborators for natural language goals


### Phase 3: Implementation
- [ ] Binary encoding/decoding (ByteArray)
- [ ] Message serialization/deserialization
- [ ] DNS cache
- [ ] Resolver state machine (RFC 1034 section 5.3.3)
- [ ] UDP/TCP transport layer

### Phase 4: Proofs
- [ ] Encode/decode roundtrip
- [ ] Message format conformance
- [ ] Resolver algorithm conformance

### Phase 5: Integration
- [ ] Executable DNS server on port 53
- [ ] Test with `dig` queries
- [ ] RESINFO support (RFC 9606)

## RFCs

- `rfc/rfc-1034.txt` - Domain Names: Concepts and Facilities
- `rfc/rfc-1035.txt` - Domain Names: Implementation and Specification
- `rfc/rfc-9606.txt` - DNS Resolver Information

## Usage

```
lake build        # build everything
lake exe veri-dns # run the resolver (once implemented)
```

## include_rfc Macro

```lean
include_rfc[1035][1401:1529] {
4.1.1. Header section format

The header contains the following fields:
...
}
```

At compile time, this loads `rfc/rfc-1035.txt`, extracts lines
1401-1529, strips page break artifacts, and checks the text matches
exactly. A mismatch produces a compile error with a diff.
