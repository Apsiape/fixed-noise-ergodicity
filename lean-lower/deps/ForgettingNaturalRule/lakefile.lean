import Lake
open Lake DSL

package ForgettingNaturalRule where
  moreLeanArgs := #["-j1", "-M5000"]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"
require FixedNoiseErgodicity from "../FixedNoiseErgodicity"
require UncomputableNoiseDiagram from "../UncomputableNoiseDiagram"

@[default_target]
lean_lib ForgettingNaturalRule where
  roots := #[]
  globs := #[.one `ForgettingNaturalRule.Coherence.Rel, .one `ForgettingNaturalRule.Coherence.Tiling, .one `ForgettingNaturalRule.Constants, .one `ForgettingNaturalRule.Forget.Paths, .one `ForgettingNaturalRule.Forget.Unique, .one `ForgettingNaturalRule.Main, .one `ForgettingNaturalRule.Memory.Branch, .one `ForgettingNaturalRule.Memory.Cover, .one `ForgettingNaturalRule.Memory.Invariant, .one `ForgettingNaturalRule.PCA.Average, .one `ForgettingNaturalRule.Reduction, .one `ForgettingNaturalRule.Rule.Bridge, .one `ForgettingNaturalRule.Rule.Local, .one `ForgettingNaturalRule.Statements]
