/-
# The domino reduction, and the printed Theorem A without hypothesis (node A4)

The paper proves Theorem A from Theorem D and the classical domino reduction of Berger and Robinson
(`FNR.DominoReduction`); `Main.lean` proves that route, `FNR.theorem_A_from_domino`. The forgetting
core proves a reduction of the same kind for the same machine model: its Theorem C (`FNE.Three.theoremC_familyR`, with `FNE.Family.computable_familyR`)
gives a total computable family `M ↦ R_M` of finite Wang sets with `R_M` tiling the plane if `M`
does not halt (`FNE.Family.tiles_of_not_halts`, `prop:tiles`) and `R_M` 3-token refutable if `M`
halts (`thm:three`), hence not tiling (Theorem B: a refutable set has an ergodic quorum rule, a
tiling set a non-ergodic one). The paper itself notes this second realization (after
`nw:machine`: "The detailed machine family `R_M` retained later is a different computable
realization"). Its tiling predicate `FNE.Tiles` is `TilesPlane` (`tilesPlane_iff`, by `Iff.rfl`).

Consequences, all without hypothesis:
* **`domino_reduction : DominoReduction`**;
* **`ergodicity_reduction : ErgodicityReduction`** and **`theorem_A : TheoremA`** (Theorem A as
  printed; `TheoremA` is `ErgodicityReduction`);
* `domino_undecidable_of_reduction` (one line: a decision of tiling and the reduction would decide
  halting, against the forgetting core's `FNE.halts_not_computable`, which is proved from
  Mathlib's `ComputablePred.halting_problem`); **`domino_undecidable : DominoUndecidable`** (Berger's
  theorem); **`ergodicity_undecidable`** (the undecidability form at every `0 < ε ≤ ε_*`);
* `machineCorollary_of_reduction`, **`machine_corollary : MachineCorollary`** (Corollary
  `nw:machine` in full).

This module imports the whole forgetting core (`FixedNoiseErgodicity.Undecidable`), whereas
`Main.lean` reaches only four of its modules (through the noise-diagram core).
-/
import ForgettingNaturalRule.Main
import FixedNoiseErgodicity.Undecidable

set_option autoImplicit false

namespace FNR

open FNE (TuringMachine WangSet)

/-- The forgetting core's tiling predicate is `TilesPlane`. -/
theorem tilesPlane_iff (R : WangSet) : TilesPlane R ↔ FNE.Tiles R := Iff.rfl

/-- **Theorem C of the forgetting core, as a tiling statement**: the family `R_M` tiles the plane
if and only if `M` does not halt. -/
theorem familyR_tiles_iff (M : TuringMachine) :
    TilesPlane (FNE.Family.familyR M).toFinset ↔ ¬ M.Halts := by
  refine ⟨fun ht hM => ?_, fun hM => FNE.Family.tiles_of_not_halts M hM⟩
  have herg := ((FNE.Three.eight_familyR FNE.eps0_pos le_rfl M).2).2 hM
  exact FNE.not_ergodic_of_tiles (by norm_num) FNE.eps0_pos (le_of_eq FNE.eps0_eq_epsK) ht herg

/-- **The classical domino reduction holds** (for the forgetting core's machine model), with the
family `R_M` of the forgetting core. -/
theorem domino_reduction : DominoReduction :=
  ⟨FNE.Family.familyR, FNE.Family.computable_familyR, familyR_tiles_iff⟩

/-- **The printed statement of Theorem A, without hypothesis**: Theorem A from the domino
reduction, applied to `domino_reduction`. -/
theorem ergodicity_reduction : ErgodicityReduction := theorem_A_from_domino domino_reduction

/-- **Theorem A on `ℤ⁶`** (introduction, `mainA`; Corollary `nw:machine`), as printed, without
hypothesis: there is a total computable map `M ↦ W_M` from Turing machines to finite Wang sets such
that, for every `ε ∈ (0, ε_*]`, `G_{W_M}` with uniform whole-symbol replacement at rate `ε` is a
positive-rate PCA, ergodic iff `M` halts. -/
theorem theorem_A : TheoremA := ergodicity_reduction

/-- A domino reduction makes the domino problem undecidable, since halting is undecidable
(`FNE.halts_not_computable`). -/
theorem domino_undecidable_of_reduction (h : DominoReduction) : DominoUndecidable := by
  obtain ⟨W, hW, hspec⟩ := h
  rintro ⟨g, hg, hgspec⟩
  apply FNE.halts_not_computable
  rw [ComputablePred.computable_iff]
  refine ⟨fun M => !g (W M), Primrec.not.to_comp.comp (hg.comp hW), ?_⟩
  funext M
  apply propext
  show M.Halts ↔ (!g (W M)) = true
  rw [Bool.not_eq_true', ← Bool.not_eq_true, hgspec (W M), hspec M, not_not]

/-- A domino reduction makes ergodicity undecidable at every fixed `0 < ε ≤ ε_*`. -/
theorem ergodicityUndecidable_of_reduction (h : DominoReduction) :
    ∀ ε : ℝ, 0 < ε → ε ≤ epsStar → ErgodicityUndecidable ε :=
  theorem_A_undecidable (domino_undecidable_of_reduction h)

/-- **Berger's theorem**: the domino problem is undecidable. -/
theorem domino_undecidable : DominoUndecidable := domino_undecidable_of_reduction domino_reduction

/-- **The undecidability form, without hypothesis**: at every fixed `0 < ε ≤ ε_*`, no algorithm
decides, given `R`, whether `G_R` is ergodic. -/
theorem ergodicity_undecidable : ∀ ε : ℝ, 0 < ε → ε ≤ epsStar → ErgodicityUndecidable ε :=
  ergodicityUndecidable_of_reduction domino_reduction

/-- Corollary `nw:machine` from a domino reduction (Theorem D for the same map, and halting is
undecidable). -/
theorem machineCorollary_of_reduction (h : DominoReduction) : MachineCorollary := by
  obtain ⟨W, hW, hspec⟩ := h
  have herg : ∀ ε : ℝ, 0 < ε → ε ≤ epsStar → ∀ M : TuringMachine,
      (natCA (W M).toFinset).IsErgodic ε ↔ M.Halts := fun ε hpos hε M => by
    rw [(natural_classification (W M).toFinset ε hpos hε).1, hspec M, not_not]
  refine ⟨W, hW, hspec, fun ε hpos hε => ⟨fun M => ⟨isPositiveRatePCA _ hpos
    (hε.trans Const.epsStar_le_one), herg ε hpos hε M⟩, ?_⟩⟩
  rintro ⟨g, hg, hgspec⟩
  apply FNE.halts_not_computable
  rw [ComputablePred.computable_iff]
  refine ⟨g, hg, funext fun M => propext ?_⟩
  rw [hgspec M, herg ε hpos hε M]

/-- **Corollary `nw:machine` in full, without hypothesis.** -/
theorem machine_corollary : MachineCorollary := machineCorollary_of_reduction domino_reduction

end FNR
