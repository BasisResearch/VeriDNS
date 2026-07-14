import VeriDNS.Impl.Parsec
import VeriDNS.Impl.DomainName
import VeriDNS.Spec.RData

namespace VeriDNS.Impl.RData

open VeriDNS.Impl
open VeriDNS.Spec

def decodeDomainNameRdata : DnsParser ByteArray := do
  let labels ← DomainName.decodeName
  return DomainName.labelsToWireFormat labels

def encodeDomainNameRdata (wire : ByteArray) : DnsSerializer Unit :=
  DnsSerializer.writeBytes wire

def decodeA : DnsParser RData.A.ARdata := do
  let addr ← readBV32
  return { address := addr }

def encodeA (r : RData.A.ARdata) : DnsSerializer Unit :=
  writeBV32 r.address

def decodeCname : DnsParser RData.Cname.CnameRdata := do
  let cname ← decodeDomainNameRdata
  return { cname := cname }

def encodeCname (r : RData.Cname.CnameRdata) : DnsSerializer Unit :=
  encodeDomainNameRdata r.cname

def decodeNs : DnsParser RData.Ns.NsRdata := do
  let nsdname ← decodeDomainNameRdata
  return { nsdname := nsdname }

def encodeNs (r : RData.Ns.NsRdata) : DnsSerializer Unit :=
  encodeDomainNameRdata r.nsdname

def decodePtr : DnsParser RData.Ptr.PtrRdata := do
  let ptrdname ← decodeDomainNameRdata
  return { ptrdname := ptrdname }

def encodePtr (r : RData.Ptr.PtrRdata) : DnsSerializer Unit :=
  encodeDomainNameRdata r.ptrdname

def decodeMb : DnsParser RData.Mb.MbRdata := do
  let madname ← decodeDomainNameRdata
  return { madname := madname }

def encodeMb (r : RData.Mb.MbRdata) : DnsSerializer Unit :=
  encodeDomainNameRdata r.madname

def decodeMd : DnsParser RData.Md.MdRdata := do
  let madname ← decodeDomainNameRdata
  return { madname := madname }

def encodeMd (r : RData.Md.MdRdata) : DnsSerializer Unit :=
  encodeDomainNameRdata r.madname

def decodeMf : DnsParser RData.Mf.MfRdata := do
  let madname ← decodeDomainNameRdata
  return { madname := madname }

def encodeMf (r : RData.Mf.MfRdata) : DnsSerializer Unit :=
  encodeDomainNameRdata r.madname

def decodeMg : DnsParser RData.Mg.MgRdata := do
  let mgmname ← decodeDomainNameRdata
  return { mgmname := mgmname }

def encodeMg (r : RData.Mg.MgRdata) : DnsSerializer Unit :=
  encodeDomainNameRdata r.mgmname

def decodeMr : DnsParser RData.Mr.MrRdata := do
  let newname ← decodeDomainNameRdata
  return { newname := newname }

def encodeMr (r : RData.Mr.MrRdata) : DnsSerializer Unit :=
  encodeDomainNameRdata r.newname

def decodeHinfo : DnsParser RData.Hinfo.HinfoRdata := do
  let cpuLen ← DnsParser.readUInt8
  let cpu ← DnsParser.readBytes cpuLen.toNat
  let osLen ← DnsParser.readUInt8
  let os ← DnsParser.readBytes osLen.toNat
  return { cpu := cpu, os := os }

def encodeHinfo (r : RData.Hinfo.HinfoRdata) : DnsSerializer Unit := do
  DnsSerializer.writeUInt8 r.cpu.size.toUInt8
  DnsSerializer.writeBytes r.cpu
  DnsSerializer.writeUInt8 r.os.size.toUInt8
  DnsSerializer.writeBytes r.os

def decodeMinfo : DnsParser RData.Minfo.MinfoRdata := do
  let rmailbx ← decodeDomainNameRdata
  let emailbx ← decodeDomainNameRdata
  return { rmailbx := rmailbx, emailbx := emailbx }

def encodeMinfo (r : RData.Minfo.MinfoRdata) : DnsSerializer Unit := do
  encodeDomainNameRdata r.rmailbx
  encodeDomainNameRdata r.emailbx

def decodeMx : DnsParser RData.Mx.MxRdata := do
  let pref ← readBV16
  let exchange ← decodeDomainNameRdata
  return { preference := pref, exchange := exchange }

def encodeMx (r : RData.Mx.MxRdata) : DnsSerializer Unit := do
  writeBV16 r.preference
  encodeDomainNameRdata r.exchange

def decodeSoa : DnsParser RData.Soa.SoaRdata := do
  let mname ← decodeDomainNameRdata
  let rname ← decodeDomainNameRdata
  let serial ← readBV32
  let refresh ← readBV32
  let retry ← readBV32
  let expire ← readBV32
  let minimum ← readBV32
  return {
    mname := mname, rname := rname,
    serial := serial, refresh := refresh,
    retry := retry, expire := expire,
    minimum := minimum
  }

def encodeSoa (r : RData.Soa.SoaRdata) : DnsSerializer Unit := do
  encodeDomainNameRdata r.mname
  encodeDomainNameRdata r.rname
  writeBV32 r.serial
  writeBV32 r.refresh
  writeBV32 r.retry
  writeBV32 r.expire
  writeBV32 r.minimum

def decodeTxt (rdlength : Nat) : DnsParser RData.Txt.TxtRdata := do
  let startPos ← DnsParser.getPos
  let mut txtData := ByteArray.empty
  while (← DnsParser.getPos) < startPos + rdlength do
    let len ← DnsParser.readUInt8
    let chunk ← DnsParser.readBytes len.toNat
    txtData := txtData ++ chunk
  return { «txt-data» := txtData }

def encodeTxt (r : RData.Txt.TxtRdata) : DnsSerializer Unit := do

  DnsSerializer.writeUInt8 r.«txt-data».size.toUInt8
  DnsSerializer.writeBytes r.«txt-data»

def decodeNull (rdlength : Nat) : DnsParser RData.Null.NullRdata := do
  let data ← DnsParser.readBytes rdlength
  return { «<anything>» := data }

def encodeNull (r : RData.Null.NullRdata) : DnsSerializer Unit :=
  DnsSerializer.writeBytes r.«<anything>»

def decodeWks (rdlength : Nat) : DnsParser RData.Wks.WksRdata := do
  let addr ← readBV32
  let proto ← readBV8
  let bitmapLen := rdlength - 5
  let bitmap ← DnsParser.readBytes bitmapLen
  return { address := addr, protocol := proto, «<bit map>» := bitmap }

def encodeWks (r : RData.Wks.WksRdata) : DnsSerializer Unit := do
  writeBV32 r.address
  writeBV8 r.protocol
  DnsSerializer.writeBytes r.«<bit map>»

end VeriDNS.Impl.RData
