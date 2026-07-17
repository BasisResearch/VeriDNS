import VeriDNS.RFC.Check
import VeriDNS.Impl.Server

/-!
# RFC 8482: minimal-sized responses to QTYPE=ANY queries

RFC 8482 (*Providing Minimal-Sized Responses to DNS Queries That Have
QTYPE=ANY*, updates RFC 1034/1035) lets a responder decline the full,
amplification-prone multi-type ANY resolution and instead return a minimal
synthesized answer.  §4.2 specifies the concrete shape: a single synthesized
HINFO resource record whose CPU field is `"RFC8482"` and whose OS field is the
null string.

`VeriDNS.Impl.Server.synthAnyResponse` is exactly this minimal response, emitted
at the serve boundary for any QTYPE=ANY query (before any resolution).  The
predicate `MinimalAnyResponse` below states the §4.2 shape, and
`synthAnyResponse_minimal` proves the implementation realizes it.
-/

namespace VeriDNS.Spec.AnyMinimal

open VeriDNS.Spec VeriDNS.Impl

include_rfc [8482][271:278] {
4.2.  Answer with a Synthesized HINFO RRset

   If there is no CNAME present at the owner name matching the QNAME,
   the resource record returned in the response MAY instead be
   synthesized.  In this case, a single HINFO resource record SHOULD be
   returned.  The CPU field of the HINFO RDATA SHOULD be set to
   "RFC8482".  The OS field of the HINFO RDATA SHOULD be set to the null
   string to minimize the size of the response.
}

/-- The RFC 8482 §4.2 minimal-response shape for a QTYPE=ANY query owned by
    `qname`: a NOERROR reply carrying exactly one answer record — a single
    synthesized HINFO RRset with CPU `"RFC8482"` and a null OS field — and no
    authority or additional records.  The single HINFO RR is the whole answer,
    which is what minimizes the response and removes the amplification vector of
    a full multi-type ANY answer. -/
def MinimalAnyResponse (qname : ByteArray) (resp : VeriDNS.Spec.Format) : Prop :=
  resp.header.rcode = Rcode.noError
  ∧ resp.header.qr = 1
  ∧ resp.answer.size = 1
  ∧ resp.authority.size = 0
  ∧ resp.additional.size = 0
  ∧ resp.answer[0]? = some
      (DnsSerializer.runBytes
        (VeriDNS.Impl.ResourceRecord.encode (Server.hinfoRFC8482RR qname)))

/-- The single answer record of the RFC 8482 minimal response, when decoded, is
    a HINFO record whose RDATA is the two character-strings CPU=`"RFC8482"` and
    OS=`""` (the null string). -/
theorem hinfoRFC8482RR_shape (qname : ByteArray) :
    (Server.hinfoRFC8482RR qname).type = Server.hinfoType
    ∧ (Server.hinfoRFC8482RR qname).«class» = Server.inClassCode
    ∧ (Server.hinfoRFC8482RR qname).rdata
        = ⟨#[7, 0x52, 0x46, 0x43, 0x38, 0x34, 0x38, 0x32, 0]⟩ :=
  ⟨rfl, rfl, rfl⟩

/-- The implementation's synthesized ANY response (`Server.synthAnyResponse`)
    realizes the RFC 8482 §4.2 minimal-response shape for the client's qname. -/
theorem synthAnyResponse_minimal (query : VeriDNS.Spec.Format) :
    MinimalAnyResponse (Server.clientQname query) (Server.synthAnyResponse query) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

rfc_proves VeriDNS.Spec.AnyMinimal.MinimalAnyResponse [8482][271:278]
  via VeriDNS.Spec.AnyMinimal.synthAnyResponse_minimal

end VeriDNS.Spec.AnyMinimal
