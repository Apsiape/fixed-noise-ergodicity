/-
# Theorem D, and Theorem A from the domino reduction (nodes A1, A2, A3)

* `FNR.natural_classification : FNR.NaturalClassification` (Theorem D): the memory branch
  (`Memory.memory_branch`), the forgetting branch (`Forget.ergodic_of_not_tiles`) and the two
  translation-invariant stationary laws on tilers (`Memory.twoTI_of_tiles`).
* `FNR.theorem_A_from_domino : FNR.TheoremAFromDomino` (Theorem A from the domino reduction, the
  route of the paper's proof; a conditional form, weaker than the printed Theorem A): the domino
  reduction `M ↦ W_M` of Berger and Robinson (`FNR.DominoReduction`, the hypothesis of
  `FNR.TheoremAFromDomino`) composed with Theorem D; the positive-rate clauses are the
  noise-diagram core's PCA layer (`isPositiveRatePCA`). The printed Theorem A, without hypothesis,
  is `FNR.theorem_A` in `Reduction.lean`.
* `FNR.theorem_A_undecidable : FNR.TheoremAUndecidable` (the undecidability form, a corollary): a
  decision procedure for ergodicity at a fixed rate would, by Theorem D, decide tiling (negated),
  against Berger's theorem `FNR.DominoUndecidable`.
-/
import ForgettingNaturalRule.Forget.Unique
import ForgettingNaturalRule.Memory.Branch
import ForgettingNaturalRule.Memory.Invariant

set_option autoImplicit false

namespace FNR

/-- Every cellular automaton with uniform whole-symbol replacement at a rate `0 < ε ≤ 1` is a
positive-rate PCA (the noise-diagram core's `apply_shift`, `apply_congr`, `law_dirac_one`,
`siteLaw_pos`). -/
theorem isPositiveRatePCA {d : ℕ} (A : UND.CA d) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    IsPositiveRatePCA A ε :=
  ⟨fun a x => A.apply_shift a x, fun _ _ _ h => A.apply_congr h,
    fun x => A.law_dirac_one h0.le h1 x, fun x w s => A.siteLaw_pos h0 x w s⟩

/-- **Theorem D** (`nw:classification` without the coalescence bound). For every finite Wang set
`R` and every `0 < ε ≤ ε_*`, `G_R` with uniform whole-symbol replacement is ergodic iff `R` does
not tile; if `R` tiles, it has two distinct translation-invariant stationary laws. -/
theorem natural_classification : NaturalClassification := fun _ _ hpos hε =>
  ⟨⟨fun herg htile => Memory.memory_branch htile hpos.le hε herg,
    fun hnt => Forget.ergodic_of_not_tiles hnt hpos.le hε⟩,
    fun htile => Memory.twoTI_of_tiles htile hpos.le hε⟩

/-- Theorem A from Theorem D and the domino reduction: the reduction composed with the
classification. -/
theorem theoremAFromDomino_of_classification (h : NaturalClassification) :
    TheoremAFromDomino := by
  rintro ⟨W, hW, hspec⟩
  refine ⟨W, hW, fun ε hpos hε M => ⟨isPositiveRatePCA _ hpos
    (hε.trans Const.epsStar_le_one), ?_⟩⟩
  rw [(h (W M).toFinset ε hpos hε).1, hspec M, not_not]

/-- **Theorem A from the domino reduction** (the route of the paper's proof of `nw:machine`; a
conditional form, weaker than the printed Theorem A). Under the classical domino reduction of
Berger and Robinson (`DominoReduction`), there is a total computable map `M ↦ W_M` from Turing
machines to finite Wang sets such that, for every `ε ∈ (0, ε_*]`, `G_{W_M}` with uniform
whole-symbol replacement at rate `ε` is a positive-rate PCA, ergodic iff `M` halts. -/
theorem theorem_A_from_domino : TheoremAFromDomino :=
  theoremAFromDomino_of_classification natural_classification

/-- The undecidability form from Theorem D: a computable decision of ergodicity at a fixed rate
gives, negated, a computable decision of tiling. -/
theorem theoremAUndecidable_of_classification (h : NaturalClassification) :
    TheoremAUndecidable := by
  intro hB ε hpos hε ⟨g, hg, hspec⟩
  apply hB
  refine ⟨fun l => !g l, Primrec.not.to_comp.comp hg, fun l => ?_⟩
  have hc := (h l.toFinset ε hpos hε).1
  show (!g l) = true ↔ TilesPlane l.toFinset
  rw [Bool.not_eq_true', ← Bool.not_eq_true, hspec l, hc, not_not]

/-- **The undecidability form** (a corollary). Under Berger's theorem (`DominoUndecidable`), at
every fixed rate `0 < ε ≤ ε_*` no algorithm decides, given `R`, whether `G_R` is ergodic. -/
theorem theorem_A_undecidable : TheoremAUndecidable :=
  theoremAUndecidable_of_classification natural_classification

end FNR
