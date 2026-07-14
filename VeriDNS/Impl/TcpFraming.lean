import VeriDNS.Impl.Message




namespace VeriDNS.Impl.TcpFraming

def lenPrefix (n : Nat) : ByteArray :=
  ⟨#[(n / 256).toUInt8, (n % 256).toUInt8]⟩

def frameTcp (payload : ByteArray) : ByteArray :=
  lenPrefix payload.size ++ payload

def unframeTcp (buf : ByteArray) : Option ByteArray :=
  if h : 2 ≤ buf.size then
    let len := (buf[0]'(by omega)).toNat * 256 + (buf[1]'(by omega)).toNat
    let body := buf.extract 2 (2 + len)
    if body.size = len then some body else none
  else none

end VeriDNS.Impl.TcpFraming
