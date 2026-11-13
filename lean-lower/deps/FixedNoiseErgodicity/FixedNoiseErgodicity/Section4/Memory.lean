/-
# Section 4 (memory): `mem:field-bound` and `thm:memory`

Printed Section 4 ("Tilings give memory", source file `03-memory.tex`), Section 4.4.
* `field_bound` (`mem:field-bound`): `P(E_t(v) = 1) ≤ ε (1 + 2λ/(1 - λ))`, by `lem:contour`
  (last assertion), `mem:count` and the Peierls sum;
* `memory` (`thm:memory`, the bounds `mem:bounds`): from a cloned tiling `ξ`,
  `P(X_t(v) ≠ ξ(v)) ≤ ε (1 + 2λ/(1 - λ)) < 1.01 ε`, and from `⊥`, `P(Y_t(v) ≠ ⊥)` obeys the same
  bound;
* `hasMemory_of_tiling` (the gap `mem:gap`): the process has memory, with window `{v}`, the event
  "`v` carries `ξ(v)`" and `α = 1 - 2.02 ε`;
* `not_ergodic_of_tiles` (Theorem B(i) as used by Theorem A): if `R` tiles, the process is not
  ergodic (via `set:memory-nonergodic`, decision D8).
-/
import FixedNoiseErgodicity.Section4.Deterministic
import FixedNoiseErgodicity.Section3.Peierls
import FixedNoiseErgodicity.Section3.Constants
import FixedNoiseErgodicity.Section2.Ergodic

set_option autoImplicit false

noncomputable section

namespace FNE

open MeasureTheory
open scoped ENNReal

variable {k : ℕ} {R : WangSet}

/-! ## `mem:field-bound` -/

/-- **`mem:field-bound`.** For `0 < ε ≤ 1` and `λ = 2 D₀² ε^{1/q²} < 1`, every site `v` and time
`t`: `P(E_t(v) = 1) ≤ ε (1 + 2λ/(1 - λ))`.
(The paper assumes `k ≥ 2` and `ε < 1`; the proof uses neither, so they are dropped.) -/
theorem field_bound {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) (hl : lam k ε < 1) (t : ℕ) (v : Site k) :
    noiseLaw k R ε {ω | domField ω.flags t v} ≤
      ENNReal.ofReal (ε * (1 + 2 * lam k ε / (1 - lam k ε))) := by
  cases t with
  | zero =>
    have : {ω : Noise k R | domField ω.flags 0 v} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact domField_zero _ v
    rw [this, measure_empty]
    exact bot_le
  | succ t =>
    have hq : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
    set A : Set (Noise k R) :=
      {ω | ∃ e : ℕ, 1 ≤ e ∧ PeierlsWitness ((v, t + 1) : STPoint k)
        (1 + 1 / ((k : ℝ) + 1) ^ 2 * (e : ℝ)) e ω} with hA
    have hsub : {ω : Noise k R | domField ω.flags (t + 1) v} ⊆
        {ω | ∀ p ∈ ({(t, v)} : Finset (ℕ × Site k)), (ω p).1 = true} ∪ A := by
      intro ω hω
      by_cases hev : (ω (t, v)).1 = true
      · left
        intro p hp
        rw [Finset.mem_singleton.mp hp]
        exact hev
      · right
        have hev' : ω.flags (t, v) = false := by simpa [Noise.flags] using hev
        obtain ⟨K, Sig, hK1, hG, hconn, -, hSigK, hSigE, hKle⟩ := contour_marked ω.flags hω hev'
        have hS1 : 1 ≤ Sig.card := by
          by_contra h
          have : Sig.card - 1 = 0 := by omega
          rw [this, mul_zero] at hKle
          omega
        refine ⟨K.card, hK1, K, rfl, hG, hconn, Sig, fun φ hφ => Or.inr (hSigK φ hφ), ?_,
          hSigE⟩
        have hKle' : (K.card : ℝ) ≤ ((k : ℝ) + 1) ^ 2 * ((Sig.card : ℝ) - 1) := by
          have := Nat.cast_le (α := ℝ).mpr hKle
          push_cast [Nat.cast_sub hS1] at this
          exact this
        have : 1 / ((k : ℝ) + 1) ^ 2 * (K.card : ℝ) ≤ (Sig.card : ℝ) - 1 := by
          rw [one_div, inv_mul_le_iff₀ hq]
          exact hKle'
        linarith
    have hl0 := lam_nonneg k h0.le
    have hA' : noiseLaw k R ε A ≤ ENNReal.ofReal (2 * ε * lam k ε / (1 - lam k ε)) := by
      have := peierls (R := R) h0 h1 1 (1 / ((k : ℝ) + 1) ^ 2) hl (v, t + 1) 1 A
        (fun ω hω => hω)
      rw [Real.rpow_one, pow_one] at this
      exact this
    calc noiseLaw k R ε {ω | domField ω.flags (t + 1) v}
        ≤ noiseLaw k R ε ({ω | ∀ p ∈ ({(t, v)} : Finset (ℕ × Site k)), (ω p).1 = true} ∪ A) :=
          measure_mono hsub
      _ ≤ noiseLaw k R ε {ω | ∀ p ∈ ({(t, v)} : Finset (ℕ × Site k)), (ω p).1 = true} +
            noiseLaw k R ε A := measure_union_le _ _
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal (2 * ε * lam k ε / (1 - lam k ε)) := by
          rw [noiseLaw_flags_eq h0.le h1, Finset.card_singleton, pow_one]
          gcongr
      _ = ENNReal.ofReal (ε * (1 + 2 * lam k ε / (1 - lam k ε))) := by
          rw [← ENNReal.ofReal_add h0.le
            (div_nonneg (by positivity) (by linarith))]
          congr 1
          ring

/-! ## `thm:memory` -/

/-- `P_x(X_t(v) ∈ B)` as a probability of the noise. -/
theorem law_dirac_apply_site {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (x : Config k R) (t : ℕ)
    (v : Site k) (B : Set (Sym R)) :
    law k R ε (Measure.dirac x) t {y | y v ∈ B} = noiseLaw k R ε {ω | run x ω t v ∈ B} := by
  have hm : Measurable (fun ω : Noise k R => run x ω t) :=
    (measurable_run t).comp measurable_prodMk_left
  have hB : MeasurableSet {y : Config k R | y v ∈ B} := by
    have h := B.to_countable.measurableSet.preimage
      (measurable_pi_apply (X := fun _ : Site k => Sym R) v)
    exact h
  rw [law_dirac h0 h1, Measure.map_apply hm hB]
  rfl

/-- **`thm:memory`**, the bounds `mem:bounds`. Let `k ≥ 2`, `0 < ε ≤ ε_k = (4 D₀²)^(-a)`,
`λ = 2 D₀² ε^{1/q²}`, let `R` tile the plane and `ξ` be a cloned tiling. Then for every site `v`
and time `t`: `P_ξ(X_t(v) ≠ ξ(v)) ≤ ε (1 + 2λ/(1 - λ))`, `P_⊥(X_t(v) ≠ ⊥) ≤ ε (1 + 2λ/(1 - λ))`,
and `ε (1 + 2λ/(1 - λ)) < 1.01 ε`. -/
theorem memory (hk : 2 ≤ k) {ε : ℝ} (h0 : 0 < ε) (hε : ε ≤ epsK k) {θ : Plane → Tile}
    (hθ : IsTiling R θ) (t : ℕ) (v : Site k) :
    law k R ε (Measure.dirac (clonedTiling k hθ)) t {y | y v ≠ clonedTiling k hθ v} ≤
        ENNReal.ofReal (ε * (1 + 2 * lam k ε / (1 - lam k ε))) ∧
      law k R ε (Measure.dirac (fun _ => Sym.bot)) t {y | y v ≠ Sym.bot} ≤
        ENNReal.ofReal (ε * (1 + 2 * lam k ε / (1 - lam k ε))) ∧
      ε * (1 + 2 * lam k ε / (1 - lam k ε)) < 1.01 * ε := by
  have h1 : ε ≤ 1 := hε.trans (epsK_le_one k)
  obtain ⟨hl, hlt⟩ := memoryBound_lt hk h0 hε
  refine ⟨?_, ?_, hlt⟩
  · have e := law_dirac_apply_site (R := R) h0.le h1 (clonedTiling k hθ) t v
      {s | s ≠ clonedTiling k hθ v}
    simp only [Set.mem_setOf_eq] at e
    rw [e]
    refine (measure_mono fun ω hω => ?_).trans (field_bound h0 h1 hl t v)
    exact dominate_cloned hθ hk ω t v hω
  · have e := law_dirac_apply_site (R := R) h0.le h1 (fun _ => Sym.bot) t v {s | s ≠ Sym.bot}
    simp only [Set.mem_setOf_eq] at e
    rw [e]
    refine (measure_mono fun ω hω => ?_).trans (field_bound h0 h1 hl t v)
    simp only [Set.mem_setOf_eq] at hω
    cases hs : run (fun _ => Sym.bot) ω t v with
    | bot => exact absurd hs hω
    | live s => exact dominate_bot hk ω t v s hs

/-- **The memory gap** (`mem:gap`, end of the proof of `thm:memory`). Under the hypotheses of
`thm:memory` the process has memory: the starts `ξ` and `⊥`, the window `{v}`, the event
"`v` carries `ξ(v)`" and `α = 1 - 2.02 ε > 0`. -/
theorem hasMemory_of_tiling (hk : 2 ≤ k) {ε : ℝ} (h0 : 0 < ε) (hε : ε ≤ epsK k)
    {θ : Plane → Tile} (hθ : IsTiling R θ) : HasMemory k R ε := by
  have h1 : ε ≤ 1 := hε.trans (epsK_le_one k)
  have hsmall : ε < 1 / 4 := by
    refine lt_of_le_of_lt hε ?_
    unfold epsK
    rw [one_div]
    refine inv_strictAnti₀ (by norm_num) ?_
    have hB : (4 : ℝ) < 4 * (50 * ((k : ℝ) + 1)) ^ 2 := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    calc (4 : ℝ) < 4 * (50 * ((k : ℝ) + 1)) ^ 2 := hB
      _ = (4 * (50 * ((k : ℝ) + 1)) ^ 2) ^ 1 := (pow_one _).symm
      _ ≤ (4 * (50 * ((k : ℝ) + 1)) ^ 2) ^ (2 * (k + 1) ^ 2 + 1) :=
          pow_le_pow_right₀ (by linarith) (by omega)
  set ξ := clonedTiling k hθ
  let v : Site k := ((0, 0), 0)
  let O : Finset (Site k) := {v}
  let E : Set (O → Sym R) := {f | f ⟨v, Finset.mem_singleton_self v⟩ = ξ v}
  have hcyl : cyl O E = {y | y v ∈ ({ξ v} : Set (Sym R))} := by
    ext y
    simp [cyl, E]
  refine ⟨ξ, fun _ => Sym.bot, O, E, 1 - 2.02 * ε, by linarith, fun t => ?_⟩
  obtain ⟨hX, hY, hlt⟩ := memory hk h0 hε hθ t v
  set b := ε * (1 + 2 * lam k ε / (1 - lam k ε)) with hb
  have hb0 : 0 ≤ b := by
    have := lam_nonneg k h0.le
    have : 2 * lam k ε / (1 - lam k ε) ≥ 0 :=
      div_nonneg (by positivity) (by linarith [(memoryBound_lt hk h0 hε).1])
    positivity
  haveI := isProbabilityMeasure_law h0.le h1 (Measure.dirac ξ) t
  -- the start `⊥`
  have hY' : (law k R ε (Measure.dirac (fun _ => Sym.bot)) t (cyl O E)).toReal ≤ b := by
    refine ENNReal.toReal_le_of_le_ofReal hb0 ((measure_mono ?_).trans hY)
    intro y hy
    rw [hcyl] at hy
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hy ⊢
    rw [hy]
    simp [ξ, clonedTiling]
  -- the start `ξ`
  have hX' : 1 - b ≤ (law k R ε (Measure.dirac ξ) t (cyl O E)).toReal := by
    have hcompl : cyl O E = {y : Config k R | y v ≠ ξ v}ᶜ := by
      rw [hcyl]
      ext y
      simp
    have hmeas : MeasurableSet {y : Config k R | y v ≠ ξ v} := by
      have h := (measurableSet_singleton (ξ v)).compl.preimage
        (measurable_pi_apply (X := fun _ : Site k => Sym R) v)
      exact h
    rw [hcompl, ← measureReal_def, probReal_compl_eq_one_sub hmeas, measureReal_def]
    have := ENNReal.toReal_le_of_le_ofReal hb0 hX
    linarith
  linarith

/-- **Theorem B(i), as used by Theorem A** (`thm:memory` with `set:memory-nonergodic`). If
`k ≥ 2`, `0 < ε ≤ ε_k` and `R` tiles the plane, the noisy quorum rule `F^[k]_R` at rate `ε` is not
ergodic. -/
theorem not_ergodic_of_tiles (hk : 2 ≤ k) {ε : ℝ} (h0 : 0 < ε) (hε : ε ≤ epsK k)
    (hR : Tiles R) : ¬ IsErgodic k R ε := by
  obtain ⟨θ, hθ⟩ := hR
  exact not_ergodic_of_memory (hasMemory_of_tiling hk h0 hε hθ)

end FNE

end
