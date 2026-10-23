import Lake
open System Lake DSL

-- (converted from lakefile.toml to add the native LZMA shim for `evaltest`; targets unchanged otherwise)
package OsuModel

@[default_target] lean_lib OsuModel

@[default_target] lean_exe nettest where
  root := `NetTest.Main

@[default_target] lean_exe bmdump where
  root := `BmDump.Main

lean_exe simtest where
  root := `SimTest.Main

/-- TRUSTED BOUNDARY: LZMA decompression of .osr payloads via the system liblzma (`c/lzma_shim.c`,
docs/model-eval.md). Only `evaltest` (which imports `OsuModel.Replay.Osr`) links it. -/
target lzma_shim.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "lzma_shim.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "lzma_shim.c"
  let leanInc := (← getLeanIncludeDir).toString
  buildO oFile srcJob #["-I", leanInc] #["-O2", "-fPIC"] "cc"

lean_exe evaltest where
  root := `EvalTest.Main
  moreLinkObjs := #[lzma_shim.o]
  moreLinkArgs := #["/usr/lib/x86_64-linux-gnu/liblzma.a"]
