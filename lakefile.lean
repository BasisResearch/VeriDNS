import Lake
open Lake DSL

package «veri-dns» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "main"

require verso from git
  "https://github.com/leanprover/verso.git" @ "v4.31.0-rc1"

@[default_target]
lean_lib VeriDNS where

lean_exe «veri-dns» where
  root := `VeriDNS.Main

extern_lib «veri-dns-ffi» (pkg) := do
  let srcFile := pkg.dir / "ffi" / "recvfrom.c"
  let oFile := pkg.buildDir / "ffi" / "recvfrom.o"
  let srcJob ← inputTextFile srcFile
  let inclDir ← getLeanIncludeDir
  let oJob ← buildO oFile srcJob #["-I", inclDir.toString, "-fPIC"] #[]
  buildStaticLib (pkg.buildDir / "lib" / "libveri-dns-ffi.a") #[oJob]
