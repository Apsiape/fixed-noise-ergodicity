/-
# Spatial averaging: translation-invariant stationary laws (generic PCA layer) (node T1)

Paper (Section 2, "Fully translation-invariant stationary laws"): "first average the Dirac law at
`θ` over larger and larger planar squares. A weak subsequential limit `ν` exists on the compact
tiling space. For each fixed planar translation `z`, the fraction of the averaging square changed
by `z` tends to zero; therefore `ν` is shift invariant … The kernel commutes with those
translations. All its time marginals and their Cesàro limits are therefore spatially invariant."

Formalization, for an arbitrary cellular automaton `A : UND.CA d` with uniform replacement at a
rate `0 ≤ ε ≤ 1` (the noise-diagram core's PCA layer, REUSE). The order of the two averages is
exchanged: a stationary law is averaged in space, one coordinate direction at a time.
* `savg μ a n = (n+1)⁻¹ Σ_{k ≤ n} μ ∘ T_{k a}⁻¹`, the average of `μ` along the direction `a`
  (`T_a x = x(· + a)` is the noise-diagram core's `UND.CA.shift`);
* its weak subsequential limits exist (compactness of the probability measures on `Σ^{ℤ^d}`, as in
  `UND.CA.exists_cesaro_limit`) and are `T_a`-invariant (`isInv_of_savg_limit`: the average and its
  translate differ by two terms out of `n + 1`, a one-dimensional telescoping sum);
* the average and its weak limits keep stationarity (`isStationary_savg`,
  `isStationary_of_weakTendsto`: `T_a` commutes with the kernel, `UND.CA.law_map_shift`, and the
  kernel is Feller, `UND.CA.PhiBCF`), invariance under every translation the initial law already
  had (`savg_isInv`, `isInv_of_weakTendsto`), and every one-site bound `μ{x(v) ∈ S} ≤ c` that holds
  at all sites (`savg_le`, `le_of_weakTendsto`);
* averaging along the `d` coordinate directions in turn gives invariance under the `d` unit
  translations, hence under all of `ℤ^d` (`isTI_of_unit`): **`exists_TI`**;
* the Cesàro limit of a start with a one-site bound at all times and sites keeps the bound
  (`exists_stationary_le`).
-/
import UncomputableNoiseDiagram.PCA.Translation

set_option autoImplicit false

noncomputable section

namespace FNR.Avg

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

variable {d : ℕ} (A : UND.CA d)

/-! ## Translations compose -/

theorem shift_shift (a b : UND.Site d) (x : A.Config) :
    A.shift a (A.shift b x) = A.shift (a + b) x := by
  funext w
  simp only [UND.CA.shift, add_assoc]

theorem map_shift_map_shift (μ : Measure A.Config) (a b : UND.Site d) :
    (μ.map (A.shift b)).map (A.shift a) = μ.map (A.shift (a + b)) := by
  rw [Measure.map_map (A.measurable_shift a) (A.measurable_shift b)]
  congr 1
  funext x
  exact shift_shift A a b x

theorem map_shift_zero (μ : Measure A.Config) : μ.map (A.shift 0) = μ := by
  have : A.shift 0 = id := by
    funext x w
    simp only [UND.CA.shift, add_zero, id]
  rw [this, Measure.map_id]

theorem isProbabilityMeasure_map_shift (μ : Measure A.Config) [IsProbabilityMeasure μ]
    (a : UND.Site d) : IsProbabilityMeasure (μ.map (A.shift a)) :=
  (Measure.isProbabilityMeasure_map_iff (A.measurable_shift a).aemeasurable).2 inferInstance

/-- `∫ f d(μ ∘ T_a⁻¹) = ∫ f ∘ T_a dμ`. -/
theorem integral_map_shift (μ : Measure A.Config) (a : UND.Site d) (f : A.Config →ᵇ ℝ) :
    ∫ y, f y ∂(μ.map (A.shift a)) =
      ∫ y, (f.compContinuous ⟨A.shift a, A.continuous_shift a⟩) y ∂μ :=
  integral_map (A.measurable_shift a).aemeasurable f.continuous.aestronglyMeasurable

/-- Invariance under every unit translation gives invariance under every translation of `ℤ^d`
(the translations leaving `μ` invariant form a subgroup). -/
theorem isTI_of_unit (μ : Measure A.Config)
    (h : ∀ i : Fin d, μ.map (A.shift (Pi.single i 1)) = μ) : A.IsTranslationInvariant μ := by
  let G : AddSubgroup (UND.Site d) :=
    { carrier := {a | μ.map (A.shift a) = μ}
      add_mem' := fun {a b} ha hb => by
        have ha' : μ.map (A.shift a) = μ := ha
        have hb' : μ.map (A.shift b) = μ := hb
        show μ.map (A.shift (a + b)) = μ
        rw [← map_shift_map_shift, hb', ha']
      zero_mem' := map_shift_zero A μ
      neg_mem' := fun {a} ha => by
        have ha' : μ.map (A.shift a) = μ := ha
        show μ.map (A.shift (-a)) = μ
        calc μ.map (A.shift (-a)) = (μ.map (A.shift a)).map (A.shift (-a)) := by rw [ha']
          _ = μ := by rw [map_shift_map_shift, neg_add_cancel, map_shift_zero] }
  have hsingle : ∀ (i : Fin d) (n : ℤ), (Pi.single i n : UND.Site d) ∈ G := by
    intro i n
    have e : (Pi.single i n : UND.Site d) = n • Pi.single i 1 := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    rw [e]
    exact G.zsmul_mem (h i) n
  intro a
  have ha : a ∈ G := by
    rw [← Finset.univ_sum_single a]
    exact G.sum_mem (fun i _ => hsingle i (a i))
  exact ha

/-! ## Averages of measures -/

/-- An average `(1/n) Σ_{k<n} ρ_k` of measures that all give `s` mass at most `c` gives `s` mass at
most `c`. -/
theorem avg_le {α : Type*} [MeasurableSpace α] (ρ : ℕ → Measure α) {n : ℕ} (hn : 1 ≤ n)
    (s : Set α) {c : ℝ≥0∞} (h : ∀ k ∈ Finset.range n, ρ k s ≤ c) :
    ((n : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range n, ρ k) s ≤ c := by
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  calc (n : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range n, ρ k s
      ≤ (n : ℝ≥0∞)⁻¹ * ∑ _k ∈ Finset.range n, c := by
        gcongr with k hk
        exact h k hk
    _ = c := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel (by exact_mod_cast (show n ≠ 0 by omega))
            (ENNReal.natCast_ne_top n), one_mul]

/-- The spatial average along the direction `a`: `(n+1)⁻¹ Σ_{k ≤ n} μ ∘ T_{k a}⁻¹`. -/
def savg (μ : Measure A.Config) (a : UND.Site d) (n : ℕ) : Measure A.Config :=
  ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range (n + 1), μ.map (A.shift (k • a))

/-- An average of probability measures is a probability measure. -/
theorem avg_univ {α : Type*} [MeasurableSpace α] (ρ : ℕ → Measure α) {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ k, ρ k Set.univ = 1) : ((n : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range n, ρ k) Set.univ = 1 := by
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  calc (n : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range n, ρ k Set.univ
      = (n : ℝ≥0∞)⁻¹ * ∑ _k ∈ Finset.range n, (1 : ℝ≥0∞) := by
        refine congrArg _ (Finset.sum_congr rfl (fun k _ => h k))
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
          ENNReal.inv_mul_cancel (by exact_mod_cast (show n ≠ 0 by omega))
            (ENNReal.natCast_ne_top n)]

theorem isProbabilityMeasure_savg (μ : Measure A.Config) [IsProbabilityMeasure μ]
    (a : UND.Site d) (n : ℕ) : IsProbabilityMeasure (savg A μ a n) :=
  ⟨avg_univ _ (by omega) (fun k => (isProbabilityMeasure_map_shift A μ (k • a)).measure_univ)⟩

theorem integral_savg (μ : Measure A.Config) [IsProbabilityMeasure μ] (a : UND.Site d) (n : ℕ)
    (f : A.Config →ᵇ ℝ) :
    ∫ y, f y ∂(savg A μ a n) =
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), ∫ y, f y ∂(μ.map (A.shift (k • a))) := by
  unfold savg
  rw [integral_smul_measure, integral_finsetSum_measure, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  intro k _
  have := isProbabilityMeasure_map_shift A μ (k • a)
  exact f.integrable _

/-- Feller compactness: the averages have a weak limit along a subsequence. -/
theorem exists_savg_limit (μ : Measure A.Config) [IsProbabilityMeasure μ] (a : UND.Site d) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ π : Measure A.Config, IsProbabilityMeasure π ∧
      FNE.WeakTendsto (fun m => savg A μ a (φ m)) π := by
  let ν : ℕ → ProbabilityMeasure A.Config := fun m =>
    ⟨savg A μ a m, isProbabilityMeasure_savg A μ a m⟩
  obtain ⟨π, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ν) (fun _ => Set.mem_univ _)
  exact ⟨φ, hφ, π, inferInstance,
    fun f => (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) f⟩

/-! ## Invariance along the averaging direction -/

/-- The average and its translate by `T_a` differ by `2‖f‖/(n+1)` at most. -/
theorem abs_integral_savg_shift_le (μ : Measure A.Config) [IsProbabilityMeasure μ]
    (a : UND.Site d) (n : ℕ) (f : A.Config →ᵇ ℝ) :
    |∫ y, (f.compContinuous ⟨A.shift a, A.continuous_shift a⟩) y ∂(savg A μ a n) -
        ∫ y, f y ∂(savg A μ a n)| ≤ 2 * ‖f‖ / ((n + 1 : ℕ) : ℝ) := by
  set g := f.compContinuous ⟨A.shift a, A.continuous_shift a⟩ with hg
  have hk : ∀ k : ℕ, ∫ y, g y ∂(μ.map (A.shift (k • a))) =
      ∫ y, f y ∂(μ.map (A.shift ((k + 1) • a))) := by
    intro k
    rw [← integral_map_shift A _ a f, map_shift_map_shift, succ_nsmul']
  rw [integral_savg A μ a n g, integral_savg A μ a n f]
  simp only [hk]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have htel := Finset.sum_range_sub
    (fun k : ℕ => ∫ y, f y ∂(μ.map (A.shift (k • a)))) (n + 1)
  rw [htel, abs_mul, abs_inv, Nat.abs_cast, ← div_eq_inv_mul]
  gcongr
  have := isProbabilityMeasure_map_shift A μ ((n + 1) • a)
  have := isProbabilityMeasure_map_shift A μ (0 • a)
  have b1 := f.norm_integral_le_norm (μ.map (A.shift ((n + 1) • a)))
  have b2 := f.norm_integral_le_norm (μ.map (A.shift (0 • a)))
  rw [Real.norm_eq_abs] at b1 b2
  calc |∫ y, f y ∂(μ.map (A.shift ((n + 1) • a))) - ∫ y, f y ∂(μ.map (A.shift (0 • a)))|
      ≤ |∫ y, f y ∂(μ.map (A.shift ((n + 1) • a)))| +
          |∫ y, f y ∂(μ.map (A.shift (0 • a)))| := abs_sub _ _
    _ ≤ 2 * ‖f‖ := by linarith

/-- Every weak limit of the averages along `a` is `T_a`-invariant. -/
theorem isInv_of_savg_limit (μ : Measure A.Config) [IsProbabilityMeasure μ] (a : UND.Site d)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) (π : Measure A.Config) [IsProbabilityMeasure π]
    (hπ : FNE.WeakTendsto (fun m => savg A μ a (φ m)) π) :
    π.map (A.shift a) = π := by
  have := isProbabilityMeasure_map_shift A π a
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  set g := f.compContinuous ⟨A.shift a, A.continuous_shift a⟩ with hg
  rw [integral_map_shift A π a f]
  have hdiff : Tendsto (fun m => ∫ y, g y ∂(savg A μ a (φ m)) - ∫ y, f y ∂(savg A μ a (φ m)))
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun m => 2 * ‖f‖ / ((φ m + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖f‖)).comp ((tendsto_add_atTop_nat 1).comp hφ)
    refine squeeze_zero_norm (fun m => ?_) hlim
    rw [Real.norm_eq_abs]
    exact abs_integral_savg_shift_le A μ a (φ m) f
  have h2 := (hπ g).sub (hπ f)
  have := tendsto_nhds_unique h2 hdiff
  linarith

/-! ## What the averages keep -/

/-- Invariance under a translation `T_b` of the averaged law passes to the averages. -/
theorem savg_isInv (μ : Measure A.Config) (a b : UND.Site d)
    (hb : μ.map (A.shift b) = μ) (n : ℕ) : (savg A μ a n).map (A.shift b) = savg A μ a n := by
  ext s hs
  rw [Measure.map_apply (A.measurable_shift b) hs]
  simp only [savg, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Measure.map_apply (A.measurable_shift b) hs, map_shift_map_shift, add_comm b (k • a),
    ← map_shift_map_shift, hb]

/-- Weak limits of `T_b`-invariant probability measures are `T_b`-invariant. -/
theorem isInv_of_weakTendsto (μs : ℕ → Measure A.Config) (π : Measure A.Config)
    [IsProbabilityMeasure π] (b : UND.Site d) (hμ : ∀ m, (μs m).map (A.shift b) = μs m)
    (h : FNE.WeakTendsto μs π) : π.map (A.shift b) = π := by
  have := isProbabilityMeasure_map_shift A π b
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  set g := f.compContinuous ⟨A.shift b, A.continuous_shift b⟩ with hg
  rw [integral_map_shift A π b f]
  have e : ∀ m, ∫ x, g x ∂(μs m) = ∫ x, f x ∂(μs m) := fun m => by
    rw [← integral_map_shift A (μs m) b f, hμ m]
  have h1 := h g
  simp only [e] at h1
  exact tendsto_nhds_unique h1 (h f)

/-- A translate of a stationary law is stationary (the kernel commutes with translations). -/
theorem isStationary_map_shift {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure A.Config)
    [IsProbabilityMeasure μ] (hμ : A.IsStationary ε μ) (c : UND.Site d) :
    A.IsStationary ε (μ.map (A.shift c)) := by
  have hμ' : A.law ε μ 1 = μ := hμ
  show A.law ε (μ.map (A.shift c)) 1 = μ.map (A.shift c)
  rw [← A.law_map_shift h0 h1 μ c 1, hμ']

/-- The averages of a stationary law are stationary. -/
theorem isStationary_savg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure A.Config)
    [IsProbabilityMeasure μ] (hμ : A.IsStationary ε μ) (a : UND.Site d) (n : ℕ) :
    A.IsStationary ε (savg A μ a n) := by
  have := isProbabilityMeasure_savg A μ a n
  have := A.isProbabilityMeasure_law h0 h1 (savg A μ a n) 1
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  have hPhi : ∀ ν : Measure A.Config,
      ∫ x, (∫ y, f y ∂(A.law ε (Measure.dirac x) 1)) ∂ν = ∫ x, (A.PhiBCF h0 h1 f) x ∂ν :=
    fun _ => rfl
  rw [A.integral_law h0 h1 _ 1 f, hPhi, integral_savg A μ a n, integral_savg A μ a n f]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have := isProbabilityMeasure_map_shift A μ (k • a)
  have hs : A.law ε (μ.map (A.shift (k • a))) 1 = μ.map (A.shift (k • a)) :=
    isStationary_map_shift A h0 h1 μ hμ (k • a)
  rw [← hPhi, ← A.integral_law h0 h1 _ 1 f, hs]

/-- Weak limits of stationary probability measures are stationary (the kernel is Feller). -/
theorem isStationary_of_weakTendsto {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (μs : ℕ → Measure A.Config) [∀ m, IsProbabilityMeasure (μs m)]
    (hμ : ∀ m, A.IsStationary ε (μs m)) (π : Measure A.Config) [IsProbabilityMeasure π]
    (h : FNE.WeakTendsto μs π) : A.IsStationary ε π := by
  have := A.isProbabilityMeasure_law h0 h1 π 1
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  have hPhi : ∀ ν : Measure A.Config,
      ∫ x, (∫ y, f y ∂(A.law ε (Measure.dirac x) 1)) ∂ν = ∫ x, (A.PhiBCF h0 h1 f) x ∂ν :=
    fun _ => rfl
  rw [A.integral_law h0 h1 π 1 f, hPhi]
  have e : ∀ m, ∫ x, (A.PhiBCF h0 h1 f) x ∂(μs m) = ∫ x, f x ∂(μs m) := fun m => by
    have hm : A.law ε (μs m) 1 = μs m := hμ m
    rw [← hPhi, ← A.integral_law h0 h1 (μs m) 1 f, hm]
  have h1' := h (A.PhiBCF h0 h1 f)
  simp only [e] at h1'
  exact tendsto_nhds_unique h1' (h f)

theorem measurableSet_site (v : UND.Site d) (S : Set A.Sym) :
    MeasurableSet {x : A.Config | x v ∈ S} :=
  (measurable_pi_apply v) (Set.toFinite S).measurableSet

/-- A one-site bound at every site passes to the averages. -/
theorem savg_le (μ : Measure A.Config) (a : UND.Site d) (n : ℕ) (S : Set A.Sym) (c : ℝ≥0∞)
    (hb : ∀ v, μ {x | x v ∈ S} ≤ c) (v : UND.Site d) : savg A μ a n {x | x v ∈ S} ≤ c := by
  unfold savg
  refine avg_le _ (by omega) _ (fun k _ => ?_)
  rw [Measure.map_apply (A.measurable_shift _) (measurableSet_site A v S)]
  exact hb (v + k • a)

/-- A one-site bound passes to weak limits (one-site cylinders are clopen). -/
theorem le_of_weakTendsto (μs : ℕ → Measure A.Config) (π : Measure A.Config)
    (h : FNE.WeakTendsto μs π) (S : Set A.Sym) (c : ℝ≥0∞) (hc : c ≠ ⊤) (v : UND.Site d)
    [IsFiniteMeasure π] (hb : ∀ m, μs m {x | x v ∈ S} ≤ c) : π {x | x v ∈ S} ≤ c := by
  have hO : v ∈ ({v} : Finset (UND.Site d)) := Finset.mem_singleton_self v
  have e : A.cyl {v} {z | z ⟨v, hO⟩ ∈ S} = {x | x v ∈ S} := by
    ext x
    simp [UND.CA.cyl]
  have hlim := h (A.cylIndicator {v} {z | z ⟨v, hO⟩ ∈ S})
  simp only [UND.CA.integral_cylIndicator, e] at hlim
  have hle : (π {x | x v ∈ S}).toReal ≤ c.toReal :=
    le_of_tendsto' hlim (fun m => ENNReal.toReal_mono hc (hb m))
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) hc).1 hle

/-! ## Translation-invariant stationary laws -/

/-- **A stationary law with a one-site bound at every site gives a translation-invariant
stationary law with the same bound**: average along the `d` coordinate directions in turn. -/
theorem exists_TI {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (π : Measure A.Config)
    [IsProbabilityMeasure π] (hπ : A.IsStationary ε π) (S : Set A.Sym) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (hb : ∀ v, π {x | x v ∈ S} ≤ c) :
    ∃ ν : Measure A.Config, IsProbabilityMeasure ν ∧ A.IsStationary ε ν ∧
      A.IsTranslationInvariant ν ∧ ∀ v, ν {x | x v ∈ S} ≤ c := by
  have key : ∀ k : ℕ, k ≤ d → ∃ ν : Measure A.Config, IsProbabilityMeasure ν ∧
      A.IsStationary ε ν ∧ (∀ v, ν {x | x v ∈ S} ≤ c) ∧
      ∀ i : Fin d, (i : ℕ) < k → ν.map (A.shift (Pi.single i 1)) = ν := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨π, inferInstance, hπ, hb, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨ν, hνp, hνs, hνb, hνi⟩ := ih (by omega)
      let a : UND.Site d := Pi.single (⟨k, hk⟩ : Fin d) 1
      obtain ⟨φ, hφ, π', hπ'p, hlim⟩ := exists_savg_limit A ν a
      have hP : ∀ m, IsProbabilityMeasure (savg A ν a (φ m)) := fun m =>
        isProbabilityMeasure_savg A ν a _
      refine ⟨π', hπ'p,
        isStationary_of_weakTendsto A h0 h1 _ (fun m => isStationary_savg A h0 h1 ν hνs a _) π'
          hlim,
        fun v => le_of_weakTendsto A _ π' hlim S c hc v (fun m => savg_le A ν a _ S c hνb v),
        fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact isInv_of_weakTendsto A _ π' _ (fun m => savg_isInv A ν a _ (hνi i hi) _) hlim
      · have hia : i = ⟨k, hk⟩ := Fin.ext hi
        subst hia
        exact isInv_of_savg_limit A ν a hφ.tendsto_atTop π' hlim
  obtain ⟨ν, hνp, hνs, hνb, hνi⟩ := key d le_rfl
  exact ⟨ν, hνp, hνs, isTI_of_unit A ν (fun i => hνi i i.isLt), hνb⟩

/-- **The Cesàro limit keeps a one-site bound**: if `P_μ(X_t(v) ∈ S) ≤ c` at every time and site,
some stationary law `π` has `π{x(v) ∈ S} ≤ c` at every site. -/
theorem exists_stationary_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure A.Config)
    [IsProbabilityMeasure μ] (S : Set A.Sym) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (hb : ∀ (t : ℕ) (v : UND.Site d), A.law ε μ t {x | x v ∈ S} ≤ c) :
    ∃ π : Measure A.Config, IsProbabilityMeasure π ∧ A.IsStationary ε π ∧
      ∀ v, π {x | x v ∈ S} ≤ c := by
  have hn : Tendsto (fun m : ℕ => m + 1) atTop atTop := tendsto_add_atTop_nat 1
  obtain ⟨φ, hφ, π, hπp, hπ⟩ := A.exists_cesaro_limit h0 h1 μ hn
  refine ⟨π, hπp, A.isStationary_of_cesaro_limit h0 h1 μ (hn.comp hφ.tendsto_atTop) π hπ,
    fun v => le_of_weakTendsto A _ π hπ S c hc v (fun m => ?_)⟩
  exact avg_le _ (by omega) _ (fun t _ => hb t v)

end FNR.Avg
