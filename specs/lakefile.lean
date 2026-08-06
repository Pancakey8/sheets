import Lake

open System Lake DSL

package sheets_specs where version := v!"0.1.0"

require "leanprover-community" / mathlib

input_file wrapper.c where
  path := "wrapper.c"
  text := true

target wrapper.o pkg : FilePath := do
  let srcJob <- wrapper.c.fetch
  let oFile := pkg.buildDir / "wrapper.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc"

@[default_target]
lean_lib Sheets where
  defaultFacets := #[`lean_lib.shared]
  moreLinkObjs := #[wrapper.o]
