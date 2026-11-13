import Lake
open Lake DSL

package UndecidablePhaseDiagram where
  moreLeanArgs := #["-j1", "-M6144"]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

-- Only this frozen statement module needs the Lean 4.35 compatibility option.
@[default_target]
lean_lib UPDStatements where
  roots := #[`UndecidablePhaseDiagram.Statements]
  moreLeanArgs := #["-Dbackward.isDefEq.respectTransparency=false"]
