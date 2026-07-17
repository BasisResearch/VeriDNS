import VeriDNS
-- Axiom-cleanliness check for the 054/062/060b/002 cluster + delivery-pin capstones.
open VeriDNS.Proof VeriDNS.Proof.SentMinimised VeriDNS.Proof.SentFresh in
#print axioms VeriDNS.Proof.SentMinimised.aclEntry_matches_iff
#print axioms VeriDNS.Proof.SentMinimised.aclEntry_matches_interval
#print axioms VeriDNS.Proof.SentMinimised.ioResumeLoop_sent_egress
#print axioms VeriDNS.Proof.SentMinimised.resolveWithIO_sent_egress
#print axioms VeriDNS.Proof.SentMinimised.ioResumeLoop_sent_minimised
#print axioms VeriDNS.Proof.SentMinimised.resolveWithIO_sent_minimised
#print axioms VeriDNS.Proof.SentMinimised.resolveWithIO_sends_frame
#print axioms VeriDNS.Proof.SentMinimised.replyForResolution_sends_frame
#print axioms VeriDNS.Proof.SentFresh.ioResumeLoop_sent_fresh
#print axioms VeriDNS.Proof.SentFresh.resolveWithIO_sent_fresh
#print axioms serveTcpDatagram_verdict_sound
#print axioms serveTcpDatagram_total
#print axioms serveDatagram_verdict_sound
#print axioms serveDatagram_total
#print axioms serveSeq_total
