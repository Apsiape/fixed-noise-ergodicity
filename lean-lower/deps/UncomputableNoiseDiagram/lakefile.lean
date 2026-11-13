import Lake
open Lake DSL

package UncomputableNoiseDiagram where
  moreLeanArgs := #["-j1", "-M5000"]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"
require FixedNoiseErgodicity from "../FixedNoiseErgodicity"
require UndecidablePhaseDiagram from "../UndecidablePhaseDiagram"

@[default_target]
lean_lib UncomputableNoiseDiagram where
  roots := #[]
  globs := #[.one `UncomputableNoiseDiagram.AuditCommand, .one `UncomputableNoiseDiagram.Contour.Coherence, .one `UncomputableNoiseDiagram.Contour.Counting, .one `UncomputableNoiseDiagram.Contour.Grouped, .one `UncomputableNoiseDiagram.Contour.RawPaths, .one `UncomputableNoiseDiagram.PCA.Attraction, .one `UncomputableNoiseDiagram.PCA.Cylinder, .one `UncomputableNoiseDiagram.PCA.Feller, .one `UncomputableNoiseDiagram.PCA.ForgetErgodic, .one `UncomputableNoiseDiagram.PCA.Markov, .one `UncomputableNoiseDiagram.PCA.Process, .one `UncomputableNoiseDiagram.PCA.Pullback, .one `UncomputableNoiseDiagram.PCA.Translation, .one `UncomputableNoiseDiagram.Parameters.Bases, .one `UncomputableNoiseDiagram.Parameters.Geometry, .one `UncomputableNoiseDiagram.Parameters.Search, .one `UncomputableNoiseDiagram.Parameters.Threshold, .one `UncomputableNoiseDiagram.Rule.CA, .one `UncomputableNoiseDiagram.Rule.Checker, .one `UncomputableNoiseDiagram.Rule.Noise, .one `UncomputableNoiseDiagram.Rule.Proposal, .one `UncomputableNoiseDiagram.Statements, .one `UncomputableNoiseDiagram.Windows]
