import Lake
open Lake DSL

package FixedNoiseErgodicity where
  moreLeanArgs := #["-j1", "-M6144"]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

@[default_target]
lean_lib FixedNoiseErgodicity where
  globs := #[`FixedNoiseErgodicity, `FixedNoiseErgodicity.+]
