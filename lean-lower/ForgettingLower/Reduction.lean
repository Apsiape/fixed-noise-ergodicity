/- Reuse the unconditional domino reduction exactly, without a tiling import hypothesis.
The classification is composed with the same unconditional computable domino family. -/
import ForgettingNaturalRule.Reduction
import ForgettingLower.Main

set_option autoImplicit false

namespace FLD

/-- The already proved domino reduction, for exactly the reused tile and machine types. -/
theorem domino_reduction : FNR.DominoReduction := FNR.domino_reduction

/-- QB R1: a raw-family decider would decide the machine-indexed subfamily. -/
theorem raw_undecidable_of_machine_corollary
    (h : Z4MachineCorollary) : Z4RawUndecidable := by
  obtain ⟨W, hW, _, h⟩ := h
  intro e he he0
  obtain ⟨_, hdec⟩ := h e he he0
  rintro ⟨g, hg, hspec⟩
  apply hdec
  exact ⟨g ∘ W, hg.comp hW, fun M => hspec (W M)⟩

/-- The same computable domino family proves the frozen machine corollary at every allowed rate. -/
theorem z4_machine_corollary : Z4MachineCorollary := by
  obtain ⟨W, hW, hspec⟩ := domino_reduction
  have herg : ∀ e : ℝ, 0 < e → e ≤ eps0 → ∀ M : FNE.TuringMachine,
      (natCA (W M).toFinset).IsErgodic e ↔ M.Halts := fun e hpos he M => by
    rw [(z4_classification.2 (W M).toFinset e hpos he).1]
    change ¬ FNR.TilesPlane (W M).toFinset ↔ M.Halts
    rw [hspec M, not_not]
  refine ⟨W, hW, hspec, fun e hpos he => ⟨fun M => ⟨FNR.isPositiveRatePCA _ hpos
    (he.trans Const.eps0_le_one), herg e hpos he M⟩, ?_⟩⟩
  rintro ⟨g, hg, hgspec⟩
  apply FNE.halts_not_computable
  rw [ComputablePred.computable_iff]
  refine ⟨g, hg, funext fun M => propext ?_⟩
  rw [hgspec M, herg e hpos he M]

/-- Fixed-rate undecidability on the raw Wang-set family, exactly QB's R1 target. -/
theorem z4_raw_undecidable : Z4RawUndecidable :=
  raw_undecidable_of_machine_corollary z4_machine_corollary

end FLD
