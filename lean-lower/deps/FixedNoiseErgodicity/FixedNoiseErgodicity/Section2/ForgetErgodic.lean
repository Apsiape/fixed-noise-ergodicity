/-
# Section 2.3: forgetting implies ergodicity (`set:forget-ergodic`)

* the mixture formula in real form, `P_μ(X_t ∈ A) = ∫ P_x(X_t ∈ A) dμ(x)`;
* `dtv(μΦ^t|_O, νΦ^t|_O) ≤ 2 δ_O(t)` for all probability measures `μ, ν` (`dtv_law_le`);
* **`set:forget-ergodic`** (`ergodic_of_forgets`): if the process forgets it is ergodic, and its
  invariant measure `π` satisfies `dtv(μΦ^t|_O, π|_O) ≤ 2 δ_O(t)`.
The invariant measure comes from `set:feller` (`exists_invariant`); convergence and uniqueness
come from the window bound and `weakTendsto_iff_dtv`.
-/
import FixedNoiseErgodicity.Section2.Feller

set_option autoImplicit false

noncomputable section

namespace FNE

open MeasureTheory Filter Topology
open scoped ENNReal

variable {k : ℕ} {R : WangSet}

/-- `x ↦ P_x(X_t ∈ A)` is measurable. -/
theorem measurable_law_dirac_apply {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (t : ℕ)
    {A : Set (Config k R)} (hA : MeasurableSet A) :
    Measurable (fun x : Config k R => law k R ε (Measure.dirac x) t A) := by
  haveI := isProbabilityMeasure_noiseLaw (k := k) (R := R) h0 h1
  have hS : MeasurableSet ((fun p : Config k R × Noise k R => run p.1 p.2 t) ⁻¹' A) :=
    measurable_run t hA
  have hfun : (fun x : Config k R => law k R ε (Measure.dirac x) t A) =
      fun x => noiseLaw k R ε (Prod.mk x ⁻¹' ((fun p : Config k R × Noise k R =>
        run p.1 p.2 t) ⁻¹' A)) := by
    funext x
    have hm : Measurable (fun ω : Noise k R => run x ω t) :=
      (measurable_run t).comp measurable_prodMk_left
    rw [law_dirac h0 h1, Measure.map_apply hm hA]
    rfl
  rw [hfun]
  exact measurable_measure_prodMk_left hS

/-- `set:def-noise`, the mixture formula in real form. -/
theorem law_toReal_eq_integral {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure (Config k R))
    [IsProbabilityMeasure μ] (t : ℕ) {A : Set (Config k R)} (hA : MeasurableSet A) :
    (law k R ε μ t A).toReal = ∫ x, (law k R ε (Measure.dirac x) t A).toReal ∂μ := by
  rw [law_apply_eq_lintegral h0 h1 μ t hA, integral_toReal
    (measurable_law_dirac_apply h0 h1 t hA).aemeasurable
    (Eventually.of_forall (fun x => by
      haveI := isProbabilityMeasure_law h0 h1 (Measure.dirac x) t
      exact measure_lt_top _ _))]

/-- From any initial law, the window probabilities stay within `δ_O(t)` of those from `⊥`. -/
theorem abs_law_sub_bot_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure (Config k R))
    [IsProbabilityMeasure μ] (O : Finset (Site k)) (t : ℕ) (E : Set (O → Sym R)) :
    |(law k R ε μ t (cyl O E)).toReal -
        (law k R ε (Measure.dirac (fun _ => Sym.bot)) t (cyl O E)).toReal| ≤
      deltaO k R ε O t := by
  set P : Config k R → ℝ := fun x => (law k R ε (Measure.dirac x) t (cyl O E)).toReal with hP
  have hPm : Measurable P :=
    ENNReal.measurable_toReal.comp (measurable_law_dirac_apply h0 h1 t (measurableSet_cyl O E))
  have hPle : ∀ x, ‖P x‖ ≤ 1 := by
    intro x
    haveI := isProbabilityMeasure_law h0 h1 (Measure.dirac x) t
    rw [Real.norm_eq_abs, abs_le]
    simp only [hP, ← measureReal_def]
    have hnn : 0 ≤ (law k R ε (Measure.dirac x) t).real (cyl O E) := measureReal_nonneg
    exact ⟨by linarith, measureReal_le_one⟩
  have hint : Integrable P μ :=
    Integrable.mono' (integrable_const 1) hPm.aestronglyMeasurable (Eventually.of_forall hPle)
  rw [law_toReal_eq_integral h0 h1 μ t (measurableSet_cyl O E)]
  have hc : (law k R ε (Measure.dirac (fun _ => Sym.bot)) t (cyl O E)).toReal =
      ∫ _, P (fun _ => Sym.bot) ∂μ := by
    rw [integral_const, probReal_univ, one_smul]
  rw [hc, ← integral_sub hint (integrable_const _)]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => P x - P (fun _ => Sym.bot))
    (C := deltaO k R ε O t) (Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs]
      exact (abs_le_dtv O _ _ E).trans (dtv_le_deltaO h0 h1 O t x)))
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

/-- Proof of `set:forget-ergodic`: `dtv(μΦ^t|_O, νΦ^t|_O) ≤ 2 δ_O(t)`. -/
theorem dtv_law_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ ν : Measure (Config k R))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (O : Finset (Site k)) (t : ℕ) :
    dtv O (law k R ε μ t) (law k R ε ν t) ≤ 2 * deltaO k R ε O t := by
  refine dtv_le_of (fun E => ?_)
  have a := abs_law_sub_bot_le h0 h1 μ O t E
  have b := abs_law_sub_bot_le h0 h1 ν O t E
  rw [abs_sub_comm] at b
  have := abs_sub_le (law k R ε μ t (cyl O E)).toReal
    (law k R ε (Measure.dirac (fun _ => Sym.bot)) t (cyl O E)).toReal
    (law k R ε ν t (cyl O E)).toReal
  linarith

/-- An invariant measure is fixed by every `Φ^t`. -/
theorem law_of_invariant {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (π : Measure (Config k R))
    [IsProbabilityMeasure π] (hπ : IsInvariant k R ε π) : ∀ t, law k R ε π t = π
  | 0 => law_zero h0 h1 π
  | t + 1 => by
    rw [law_succ h0 h1 t π, law_of_invariant h0 h1 π hπ t]
    exact hπ

/-- **`set:forget-ergodic`.** If the process forgets, it is ergodic. Its invariant measure `π`
satisfies `dtv(μΦ^t|_O, π|_O) ≤ 2 δ_O(t)` for every probability measure `μ`, every window `O`
and every `t ≥ 0`. -/
theorem ergodic_of_forgets {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hf : Forgets k R ε) :
    IsErgodic k R ε ∧
      ∀ π : Measure (Config k R), IsProbabilityMeasure π → IsInvariant k R ε π →
        ∀ μ : Measure (Config k R), IsProbabilityMeasure μ → ∀ (O : Finset (Site k)) (t : ℕ),
          dtv O (law k R ε μ t) π ≤ 2 * deltaO k R ε O t := by
  have hbound : ∀ π : Measure (Config k R), IsProbabilityMeasure π → IsInvariant k R ε π →
      ∀ μ : Measure (Config k R), IsProbabilityMeasure μ → ∀ (O : Finset (Site k)) (t : ℕ),
        dtv O (law k R ε μ t) π ≤ 2 * deltaO k R ε O t := by
    intro π _ hπ μ _ O t
    have := dtv_law_le h0 h1 μ π O t
    rwa [law_of_invariant h0 h1 π hπ t] at this
  refine ⟨?_, hbound⟩
  obtain ⟨π, hπp, hπ⟩ := exists_invariant (k := k) (R := R) h0 h1
  have hconv : ∀ μ : Measure (Config k R), IsProbabilityMeasure μ →
      WeakTendsto (fun t => law k R ε μ t) π := by
    intro μ hμ
    haveI : ∀ t, IsProbabilityMeasure (law k R ε μ t) := fun t => isProbabilityMeasure_law h0 h1 μ t
    rw [weakTendsto_iff_dtv]
    intro O
    have h2 : Tendsto (fun t => 2 * deltaO k R ε O t) atTop (𝓝 0) := by
      simpa using (hf O).const_mul 2
    exact squeeze_zero (fun t => dtv_nonneg _ _ _) (fun t => hbound π hπp hπ μ hμ O t) h2
  refine ⟨π, hπp, hπ, fun π' hπ'p hπ' => ?_, hconv⟩
  have hw := hconv π' hπ'p
  have hconst : (fun t => law k R ε π' t) = fun _ => π' := funext (law_of_invariant h0 h1 π' hπ')
  rw [hconst] at hw
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure
    (fun f => tendsto_nhds_unique tendsto_const_nhds (hw f))

/-! ## `set:memory-nonergodic` as printed: two invariant measures -/

/-- **`set:memory-nonergodic`** (as printed). If the process has memory, it has two different
invariant probability measures: the limits of the averages of `set:feller` from the two starts,
along a common subsequence, differ on the cylinder that witnesses the memory. -/
theorem two_invariant_of_memory {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (h : HasMemory k R ε) :
    ∃ π π' : Measure (Config k R), IsProbabilityMeasure π ∧ IsInvariant k R ε π ∧
      IsProbabilityMeasure π' ∧ IsInvariant k R ε π' ∧ π ≠ π' := by
  obtain ⟨x, x', O, E, α, hα, hmem⟩ := h
  obtain ⟨φ₁, hφ₁, π, hπp, hπ⟩ := exists_cesaro_limit (k := k) (R := R) h0 h1
    (Measure.dirac x) (n := id) tendsto_id
  obtain ⟨φ₂, hφ₂, π', hπ'p, hπ'⟩ := exists_cesaro_limit (k := k) (R := R) h0 h1
    (Measure.dirac x') (n := φ₁) hφ₁.tendsto_atTop
  have hπ2 : WeakTendsto (fun m => cesaro k R ε (Measure.dirac x) (φ₁ (φ₂ m))) π :=
    fun f => (hπ f).comp hφ₂.tendsto_atTop
  have hN : Tendsto (fun m => φ₁ (φ₂ m)) atTop atTop :=
    hφ₁.tendsto_atTop.comp hφ₂.tendsto_atTop
  refine ⟨π, π', hπp, isInvariant_of_cesaro_limit h0 h1 _ hN π hπ2, hπ'p,
    isInvariant_of_cesaro_limit h0 h1 _ hN π' hπ', fun heq => ?_⟩
  have hgap : ∀ N : ℕ, 1 ≤ N → α ≤ ∫ y, cylIndicator O E y ∂(cesaro k R ε (Measure.dirac x) N) -
      ∫ y, cylIndicator O E y ∂(cesaro k R ε (Measure.dirac x') N) := by
    intro N hN1
    rw [integral_cesaro h0 h1, integral_cesaro h0 h1]
    simp only [integral_cylIndicator]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    have hsum : (N : ℝ) * α ≤ ∑ t ∈ Finset.range N,
        ((law k R ε (Measure.dirac x) t (cyl O E)).toReal -
          (law k R ε (Measure.dirac x') t (cyl O E)).toReal) := by
      calc (N : ℝ) * α = ∑ _t ∈ Finset.range N, α := by simp
        _ ≤ _ := Finset.sum_le_sum (fun t _ => by linarith [hmem t])
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [le_inv_mul_iff₀ hNpos]
    linarith
  have hlim := (hπ2 (cylIndicator O E)).sub (hπ' (cylIndicator O E))
  have hge : α ≤ ∫ y, cylIndicator O E y ∂π - ∫ y, cylIndicator O E y ∂π' := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [hN.eventually_ge_atTop 1] with m hm
    exact hgap _ hm
  rw [heq, sub_self] at hge
  linarith

end FNE

end
