import VeriDNS.Test.IdEntropy


def main : IO UInt32 := do
  try
    VeriDNS.Test.IdEntropy.run
    IO.println "id-entropy-test: PASS"
    return 0
  catch e =>
    IO.eprintln s!"{e}"
    return 1
