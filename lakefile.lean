import Lake
open Lake DSL

package «veri-dns» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "main"

require verso from git
  "https://github.com/BasisResearch/verso" @ "main"

@[default_target]
lean_lib VeriDNS where

lean_exe «veri-dns» where
  root := `VeriDNS.Main

lean_exe «exchange-junk-test» where
  root := `VeriDNS.Test.ExchangeJunkMain

lean_exe «id-entropy-test» where
  root := `VeriDNS.Test.IdEntropyMain

/-- 060c reply-assembly bench (not in the default build). -/
lean_exe «bench-scrub» where
  root := `VeriDNS.Test.BenchScrubMain

extern_lib «veri-dns-ffi» (pkg) := do
  let srcFile := pkg.dir / "ffi" / "recvfrom.c"
  let oFile := pkg.buildDir / "ffi" / "recvfrom.o"
  let srcJob ← inputTextFile srcFile
  let inclDir ← getLeanIncludeDir
  let oJob ← buildO oFile srcJob #["-I", inclDir.toString, "-fPIC"] #[]
  buildStaticLib (pkg.buildDir / "lib" / "libveri-dns-ffi.a") #[oJob]
