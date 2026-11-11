/-
# Root module

Imports the whole formalization: the final theorem `FNE.cor_eight : FNE.CorEight` (`Main.lean`,
the statement in `Statements.lean`), the D1 bridge (`Bridge.lean`, the compiler in `Compiler/`,
and the undecidability theorems in `Undecidable.lean`) and the axiom audit (`Audit.lean`).
-/
import FixedNoiseErgodicity.Main
import FixedNoiseErgodicity.Bridge
import FixedNoiseErgodicity.Undecidable
import FixedNoiseErgodicity.Audit

set_option autoImplicit false
