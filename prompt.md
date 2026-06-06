Hi Claude! Today I'd like to implement a DNS resolver.

The difference in this one is that this will be a verified DNS resolver!

Verified to what spec? Glad you asked! It will be verified w.r.t the
RFC documents themselves! The idea is that we're going to implement
custom syntax/parsers for semi-formal text as present in RFCs such
that the natural language will produce a theorem. We want to implement
this with de-elaborators such that the goals themselves even look like
Natural language.

Now we're going to work towards this slowly.

Please start by setting up a lake project and organising the files.

I have downloaded the relevant RFCs for DNS to this document.

First setup. I want a generic mechanism that does something like:

```lean
include_rfc[number][from:to] {
...
}
```

This contains some RFC text in the ..., and at compile/elaboration
time, checks that the text is equal EXACTLY to the text in the RFC.

Our goal is to add custom parsers etc. such that this text will
verbatim be translated to specs that we can verify our implementation
to.

Please read through the RFCs (we might want to group the RFCs in a rfc
folder for the macro etc). And plan out the place where we will draw
the specs for each part of our dns resolver. Our final goal should be
something like we can run dig against our resolver, and verify it
w.r.t the spec.
