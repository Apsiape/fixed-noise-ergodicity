/-
# The D1 bridge (session 9; completed in session 10): "undecidable" as a theorem

`cor:eight` says that `F^[6]_{R_M}` is ergodic iff `M` halts. The word "undecidable" of the title
becomes a theorem once halting of the list-encoded machines (`TuringMachine`, decision D1) is known
not to be a computable predicate. This file proves the two reductions around that fact:
* `not_computable_ergodic_of`, `not_computable_ergodic`: if `TuringMachine.Halts` is not a
  computable predicate, then for every `0 < ε ≤ ε₀`, ergodicity of `F^[6]_{R_M}` is not a
  computable predicate of `M` (for `R_M`, and for every family with the dichotomy of `cor:eight`);
* `not_computable_halts_of_compiler`: `TuringMachine.Halts` is not computable as soon as some
  computable map `c ↦ M_c` from Mathlib's codes `Nat.Partrec.Code` makes `M_c` halt iff `c` halts
  on input `0` (Mathlib's `ComputablePred.halting_problem`);
* `cor_eight_undecidable_of_compiler`: both together.

The compiler is `Compiler.compiler` (`Compiler/Universal.lean`, session 10); the final theorems
(`halts_not_computable`, `cor_eight_undecidable`, `cor_eight_undecidable_statement`) are in
`Undecidable.lean`.
-/
import FixedNoiseErgodicity.Main
import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce

set_option autoImplicit false

namespace FNE

open Nat.Partrec

/-- If halting is not computable, ergodicity is not computable for any family with the dichotomy
of `cor:eight`. -/
theorem not_computable_ergodic_of {Rfam : TuringMachine → List Tile} {ε : ℝ}
    (hR : ∀ M : TuringMachine, IsErgodic 6 (Rfam M).toFinset ε ↔ M.Halts)
    (hH : ¬ ComputablePred TuringMachine.Halts) :
    ¬ ComputablePred fun M : TuringMachine => IsErgodic 6 (Rfam M).toFinset ε := by
  intro hc
  have e : (fun M : TuringMachine => IsErgodic 6 (Rfam M).toFinset ε) = TuringMachine.Halts :=
    funext fun M => propext (hR M)
  rw [e] at hc
  exact hH hc

/-- If halting is not computable, then for every `0 < ε ≤ ε₀` ergodicity of `F^[6]_{R_M}` is not a
computable predicate of `M`. -/
theorem not_computable_ergodic {ε : ℝ} (h0 : 0 < ε) (hε : ε ≤ eps0)
    (hH : ¬ ComputablePred TuringMachine.Halts) :
    ¬ ComputablePred fun M : TuringMachine => IsErgodic 6 (Family.familyR M).toFinset ε :=
  not_computable_ergodic_of (fun M => (Three.eight_familyR h0 hε M).2) hH

/-- A computable compiler from Mathlib's codes that preserves halting (on input `0`) shows that
halting of `TuringMachine` is not computable. -/
theorem not_computable_halts_of_compiler (f : Code → TuringMachine) (hf : Computable f)
    (hH : ∀ c, (f c).Halts ↔ (c.eval 0).Dom) : ¬ ComputablePred TuringMachine.Halts := fun h =>
  ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible ⟨f, hf, fun c => (hH c).symm⟩ h)

/-- **`cor_eight_undecidable` from a compiler**: given a computable halting-preserving compiler
from Mathlib's codes, for every `0 < ε ≤ ε₀` no computable predicate of `M` decides whether
`F^[6]_{R_M}` is ergodic. -/
theorem cor_eight_undecidable_of_compiler (f : Code → TuringMachine) (hf : Computable f)
    (hH : ∀ c, (f c).Halts ↔ (c.eval 0).Dom) {ε : ℝ} (h0 : 0 < ε) (hε : ε ≤ eps0) :
    ¬ ComputablePred fun M : TuringMachine => IsErgodic 6 (Family.familyR M).toFinset ε :=
  not_computable_ergodic h0 hε (not_computable_halts_of_compiler f hf hH)

end FNE
