import Lake
open Lake DSL

package ForgettingLower where
  moreLeanArgs := #["-j1", "-M5000"]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"
require FixedNoiseErgodicity from "deps/FixedNoiseErgodicity"
require ForgettingNaturalRule from "deps/ForgettingNaturalRule"
require UncomputableNoiseDiagram from "deps/UncomputableNoiseDiagram"
require UndecidablePhaseDiagram from "deps/UndecidablePhaseDiagram"

@[default_target]
lean_lib ForgettingLower where
  globs := #[`ForgettingLower, `ForgettingLower.+]
