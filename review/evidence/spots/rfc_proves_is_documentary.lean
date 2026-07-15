import VeriDNS.RFC.Check

/-
SPOT round 9 — meta-finding: `rfc_proves` performs NO semantic verification.

`elabRfcProves` (RFC/Check.lean:270-299) only (1) resolves the decl name (checks
it exists), (2) extracts the cited RFC line range (checks the range is valid),
(3) registers documentation spans. It never relates the decl's DEFINITION to the
RFC text.  So a definition with completely wrong semantics "proves" the RFC
clause as long as the name exists and the line numbers are valid.

Here `bogusFold` is the CONSTANT-ZERO function — it does no case folding at all.
We tag it against RFC 1034 lines 378-396, the exact same lines the real model
fold `Net.foldByte` is tagged with.  If this file elaborates without error, the
`rfc_proves` mechanism is documentary, not a verifier.
-/

namespace SpotRfcProves

def bogusFold : UInt8 → UInt8 := fun _ => 0

end SpotRfcProves

-- Same RFC anchor as VeriDNS.Spec.Net.foldByte (NetworkModel.lean:25).
rfc_proves SpotRfcProves.bogusFold [1034][378:396]

-- If we reached here, a constant-0 "fold" was accepted as proving the
-- case-insensitive-comparison RFC clause.
#check @SpotRfcProves.bogusFold
