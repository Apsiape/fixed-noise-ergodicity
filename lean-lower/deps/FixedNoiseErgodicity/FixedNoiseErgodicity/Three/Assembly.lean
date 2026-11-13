/-
# Theorem C with `thm:three` for the paper's family, and `cor:eight` up to computability

* **Theorem C for `R_M`** (`theoremC_familyR`): `R_M` is `3`-token refutable if `M` halts
  (`three_tokens`, `thm:three`) and tiles the plane if `M` does not halt (`tiles_of_not_halts`,
  `prop:tiles`).
* **Theorem A on `ℤ⁸` for `R_M`** (`eight_familyR`): for every `0 < ε ≤ ε₀`, the noisy quorum rule
  `F^[6]_{R_M}` is a positive-rate PCA, ergodic iff `M` halts.
* **`cor:eight` from computability** (`cor_eight_of_computable`): the printed statement of
  `cor:eight` (`CorEight`, `Statements.lean`) follows from `Computable familyR`, which is proved in
  `Family/Computable.lean`; the final theorem is `FNE.cor_eight` (`Main.lean`).
-/
import FixedNoiseErgodicity.Three.Board
import FixedNoiseErgodicity.TheoremB

set_option autoImplicit false

namespace FNE.Three

open FNE FNE.Family FNE.TokenGame

/-- **Theorem C with `thm:three`**, for the family `R_M` of `def:family`. -/
theorem theoremC_familyR (M : TuringMachine) :
    (M.Halts → Refutable (familyR M).toFinset 3) ∧ (¬ M.Halts → Tiles (familyR M).toFinset) :=
  ⟨three_tokens M, tiles_of_not_halts M⟩

/-- **Theorem A on `ℤ⁸` for `R_M`** (`cor:eight` without the computability clause): for every
`0 < ε ≤ ε₀` and every machine `M`, `F^[6]_{R_M}` is a positive-rate PCA, and it is ergodic iff `M`
halts. -/
theorem eight_familyR {ε : ℝ} (h0 : 0 < ε) (hε : ε ≤ eps0) (M : TuringMachine) :
    IsPositiveRatePCA 6 (familyR M).toFinset ε ∧ (IsErgodic 6 (familyR M).toFinset ε ↔ M.Halts) :=
  eight_of_dichotomy (three_tokens M) (tiles_of_not_halts M) h0 hε

/-- **`cor:eight` from `Computable familyR`**: the statement `FNE.CorEight`, with the family
`R_M` of `def:family` as the witness. -/
theorem cor_eight_of_computable (hcomp : Computable familyR) :
    ∃ Rfam : TuringMachine → List Tile, Computable Rfam ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ eps0 → ∀ M : TuringMachine,
        IsPositiveRatePCA 6 (Rfam M).toFinset ε ∧
          (IsErgodic 6 (Rfam M).toFinset ε ↔ M.Halts) :=
  cor_eight_of_theoremC ⟨familyR, hcomp, theoremC_familyR⟩

end FNE.Three
