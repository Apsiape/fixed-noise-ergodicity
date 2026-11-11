/-
# Theorem B, the two halves of Theorem A, and the interface to the construction

This file closes the noise half of the paper (Sections 2–4) and states what the construction
(Sections 5–9, Theorem C) must provide.
* `theoremB`: Theorem B of the introduction (`thm:memory`, `thm:forgetting`) with the paper's
  quantifiers: `j ≥ 1`, `k ≥ max(2, 2j)`, `0 < ε ≤ ε_k`, every finite Wang set `R`;
* `not_ergodic_of_tiles` (in `Section4/Memory.lean`) and `ergodic_of_refutable`: the two halves
  of Theorem A as conditional theorems;
* `eight_of_dichotomy`: Theorem A for one Wang set on `ℤ⁸` (`j = 3`, `k = 6`, `ε ≤ ε₀`);
* `cor_eight_of_theoremC`: the statement of `cor:eight` follows from Theorem C in the form
  "a computable family `M ↦ R_M` with `R_M` 3-token refutable when `M` halts and tiling the
  plane when `M` does not halt". The construction sessions must prove that hypothesis.
-/
import FixedNoiseErgodicity.Section4.Memory
import FixedNoiseErgodicity.Section3.Forgetting
import FixedNoiseErgodicity.Section2.ForgetErgodic
import FixedNoiseErgodicity.Section2.PCA

set_option autoImplicit false

noncomputable section

namespace FNE

open MeasureTheory TokenGame
open scoped ENNReal

variable {k : ℕ} {R : WangSet} {j : ℕ}

/-- **Theorem A, the halting half, as a conditional theorem** (`thm:forgetting` with
`set:forget-ergodic`). If `k ≥ 2j`, `0 < ε ≤ ε_k` and `R` is `j`-token refutable, the noisy quorum
rule `F^[k]_R` at rate `ε` is ergodic. -/
theorem ergodic_of_refutable (hk : 2 * j ≤ k) (hR : Refutable R j) {ε : ℝ} (h0 : 0 < ε)
    (hε : ε ≤ epsK k) : IsErgodic k R ε := by
  obtain ⟨r, τ, hτ⟩ := hR
  have h1 : ε ≤ 1 := hε.trans (epsK_le_one k)
  have hβ : beta k ε < 1 := (beta_le_half h0 hε).trans_lt (by norm_num)
  exact (ergodic_of_forgets h0.le h1 (forgets_of_refutable hk ⟨r, hτ⟩ h0 h1 hβ)).1

/-- **Theorem B** (`thm:memory`, `thm:forgetting`). Fix `j ≥ 1`, `k ≥ max(2, 2j)` and
`0 < ε ≤ ε_k = (4 D₀²)^(-a)`. For every finite Wang set `R`:
(i) if `R` tiles the plane, then from every cloned tiling `ξ` each site keeps its symbol, and from
`⊥` each site stays `⊥`, except with probability `< 1.01 ε` at every time; the noisy quorum rule
of `R` has memory (it remembers a bit forever), has two distinct invariant measures, and is not
ergodic;
(ii) if `R` is `j`-token refutable, then for some refutation time `τ` and `β = 2 D₀² ε^{1/a} ≤ 1/2`,
`P(X_t(v) ≠ Y_t(v)) ≤ 2 ε^{-τ/a} β^t / (1 - β)` under the common-noise coupling and
`δ_O(t) ≤ 2 |O| ε^{-τ/a} β^t / (1 - β)` for every window `O` (it forgets exponentially fast after
a delay set by the refutation); the rule forgets and is ergodic. -/
theorem theoremB (hj : 1 ≤ j) (hk : max 2 (2 * j) ≤ k) {ε : ℝ} (h0 : 0 < ε) (hε : ε ≤ epsK k)
    (R : WangSet) :
    (Tiles R →
      (∀ (θ : Plane → Tile) (hθ : IsTiling R θ) (t : ℕ) (v : Site k),
        law k R ε (Measure.dirac (clonedTiling k hθ)) t {y | y v ≠ clonedTiling k hθ v} <
          ENNReal.ofReal (1.01 * ε) ∧
        law k R ε (Measure.dirac (fun _ => Sym.bot)) t {y | y v ≠ Sym.bot} <
          ENNReal.ofReal (1.01 * ε)) ∧
      HasMemory k R ε ∧
      (∃ π π' : Measure (Config k R), IsProbabilityMeasure π ∧ IsInvariant k R ε π ∧
        IsProbabilityMeasure π' ∧ IsInvariant k R ε π' ∧ π ≠ π') ∧
      ¬ IsErgodic k R ε) ∧
    (Refutable R j →
      beta k ε ≤ 1 / 2 ∧
      ∃ τ : ℕ,
        (∀ (x : Config k R) (v : Site k) (t : ℕ),
          noiseLaw k R ε {ω | run x ω t v ≠ run (fun _ => Sym.bot) ω t v} ≤
            ENNReal.ofReal (2 * ε ^ (-(τ : ℝ) / (2 * ((k : ℝ) + 1) ^ 2 + 1)) * beta k ε ^ t /
              (1 - beta k ε))) ∧
        (∀ (O : Finset (Site k)) (t : ℕ),
          deltaO k R ε O t ≤ 2 * O.card * ε ^ (-(τ : ℝ) / (2 * ((k : ℝ) + 1) ^ 2 + 1)) *
            beta k ε ^ t / (1 - beta k ε)) ∧
        Forgets k R ε ∧ IsErgodic k R ε) := by
  have hk2 : 2 ≤ k := le_trans (le_max_left _ _) hk
  have hkj : 2 * j ≤ k := le_trans (le_max_right _ _) hk
  have h1 : ε ≤ 1 := hε.trans (epsK_le_one k)
  refine ⟨fun hR => ⟨fun θ hθ t v => ?_, ?_, ?_, not_ergodic_of_tiles hk2 h0 hε hR⟩,
    fun hR => ?_⟩
  · obtain ⟨hX, hY, hlt⟩ := memory hk2 h0 hε hθ t v
    have hlt' : ENNReal.ofReal (ε * (1 + 2 * lam k ε / (1 - lam k ε))) <
        ENNReal.ofReal (1.01 * ε) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hlt
    exact ⟨hX.trans_lt hlt', hY.trans_lt hlt'⟩
  · obtain ⟨θ, hθ⟩ := hR
    exact hasMemory_of_tiling hk2 h0 hε hθ
  · obtain ⟨θ, hθ⟩ := hR
    exact two_invariant_of_memory h0.le h1 (hasMemory_of_tiling hk2 h0 hε hθ)
  · have hβ2 := beta_le_half h0 hε
    have hβ : beta k ε < 1 := hβ2.trans_lt (by norm_num)
    obtain ⟨r, τ, hτ⟩ := hR
    have hRτ : RefutableWithTime R j τ := ⟨r, hτ⟩
    -- `j ≥ 1` is part of the paper's hypotheses; the proof does not need it
    have _hj := hj
    exact ⟨hβ2, τ, fun x v t => forgetting hkj hRτ h0 h1 hβ x v t,
      fun O t => forgetting_tv hkj hRτ h0 h1 hβ O t, forgets_of_refutable hkj hRτ h0 h1 hβ,
      ergodic_of_refutable hkj ⟨r, τ, hτ⟩ h0 hε⟩

/-- **Theorem A for one Wang set, on `ℤ⁸`** (`k = 6`, `j = 3`, `ε₀ = ε_6`). Let `0 < ε ≤ ε₀` and
let `P` be a proposition such that `R` is 3-token refutable if `P` holds and tiles the plane if
`P` fails. Then the noisy quorum rule `F^[6]_R` at rate `ε` is a positive-rate probabilistic
cellular automaton, and it is ergodic if and only if `P`. -/
theorem eight_of_dichotomy {P : Prop} (hrefute : P → Refutable R 3) (htile : ¬ P → Tiles R)
    {ε : ℝ} (h0 : 0 < ε) (hε : ε ≤ eps0) :
    IsPositiveRatePCA 6 R ε ∧ (IsErgodic 6 R ε ↔ P) := by
  rw [eps0_eq_epsK] at hε
  have h1 : ε ≤ 1 := hε.trans (epsK_le_one 6)
  refine ⟨isPositiveRatePCA h0 h1, fun herg => ?_, fun hP => ergodic_of_refutable (by norm_num)
    (hrefute hP) h0 hε⟩
  by_contra hP
  exact not_ergodic_of_tiles (by norm_num) h0 hε (htile hP) herg

/-- **`cor:eight` from Theorem C** (the interface for the construction sessions). If some total
computable map `M ↦ R_M` (Wang sets as lists of tiles) makes `R_M` 3-token refutable when `M`
halts and makes `R_M` tile the plane when `M` does not halt (Theorem C with `thm:three`), then the
statement of `cor:eight` holds, with the same family. -/
theorem cor_eight_of_theoremC
    (hC : ∃ Rfam : TuringMachine → List Tile, Computable Rfam ∧ ∀ M : TuringMachine,
      (M.Halts → Refutable (Rfam M).toFinset 3) ∧ (¬ M.Halts → Tiles (Rfam M).toFinset)) :
    ∃ Rfam : TuringMachine → List Tile, Computable Rfam ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ eps0 → ∀ M : TuringMachine,
        IsPositiveRatePCA 6 (Rfam M).toFinset ε ∧
          (IsErgodic 6 (Rfam M).toFinset ε ↔ M.Halts) := by
  obtain ⟨Rfam, hcomp, hfam⟩ := hC
  exact ⟨Rfam, hcomp, fun ε h0 hε M => eight_of_dichotomy (hfam M).1 (hfam M).2 h0 hε⟩

end FNE

end
