import VeriDNS.Test.ExchangeJunk


def main : IO UInt32 := do
  try
    VeriDNS.Test.ExchangeJunk.run
    IO.println "exchange-junk-test: PASS (3/3)"
    return 0
  catch e =>
    IO.eprintln s!"{e}"
    return 1
