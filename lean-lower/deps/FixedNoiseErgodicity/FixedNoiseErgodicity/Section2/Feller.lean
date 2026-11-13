/-
# Section 2.3: the Feller property, invariant measures, and weak convergence on cylinders

* continuity of the rule and of the process in the start (product topology);
* `Phi`: `Φf(x) = E_x f(X_1)`; `integral_law`: `∫ f d(μΦ^t) = ∫ (∫ f d(δ_xΦ^t)) dμ(x)`;
* **`set:feller`**: `Φf` is continuous for every continuous `f` (`continuous_Phi`); the Cesàro
  averages `μ̄_n = (1/n) Σ_{t<n} μΦ^t` have a weak limit along a subsequence of every
  `n_m → ∞` (`exists_cesaro_limit`), and every such limit is invariant
  (`isInvariant_of_cesaro_limit`); so an invariant probability measure exists
  (`exists_invariant`);
* the paragraph after `set:def-ergodic`: for probability measures, `μ_t → π` weakly iff
  `μ_t(cyl O ℰ) → π(cyl O ℰ)` for every window `O` and `ℰ ⊆ 𝒜_R^O` (`weakTendsto_iff_cyl`), iff
  `dtv(μ_t|_O, π|_O) → 0` for every window (`weakTendsto_iff_dtv`). The proof approximates a
  continuous function uniformly by functions of finitely many coordinates (compactness of `Ω`).

**[choice]** `set:feller` is stated for every continuous `f : Ω → ℝ`; since `Ω` is compact these
are the bounded continuous functions.
-/
import FixedNoiseErgodicity.Section2.Markov
import FixedNoiseErgodicity.Section2.Ergodic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section

namespace FNE

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

variable {k : ℕ} {R : WangSet}

/-! ## Continuity of the rule and of the process -/

/-- A function of configurations that only reads a finite window is continuous. -/
theorem continuous_of_local {β : Type*} [TopologicalSpace β] (W : Finset (Site k))
    (f : Config k R → β) (hf : ∀ y y' : Config k R, (∀ w ∈ W, y w = y' w) → f y = f y') :
    Continuous f := by
  classical
  let ext : (W → Sym R) → Config k R := fun z w => if h : w ∈ W then z ⟨w, h⟩ else .bot
  let r : Config k R → (W → Sym R) := fun y w => y w.1
  have hr : Continuous r := continuous_pi (fun w => continuous_apply w.1)
  have heq : f = (fun z => f (ext z)) ∘ r := by
    funext y
    exact hf _ _ (fun w hw => by simp [ext, r, hw])
  rw [heq]
  exact continuous_of_discreteTopology.comp hr

theorem continuous_quorumRule_apply (v : Site k) :
    Continuous (fun x : Config k R => quorumRule k R x v) :=
  continuous_of_local (window v) _ fun _ _ h => quorumRule_local fun d hd i =>
    h _ (Finset.mem_image.mpr ⟨(d, i), Finset.mem_product.mpr ⟨hd, Finset.mem_univ _⟩, rfl⟩)

theorem continuous_quorumRule : Continuous (quorumRule k R) :=
  continuous_pi continuous_quorumRule_apply

/-- For a fixed noise, `X_t` is a continuous function of the start. -/
theorem continuous_run (ω : Noise k R) (t : ℕ) : Continuous (fun x : Config k R => run x ω t) := by
  induction t with
  | zero => exact continuous_id
  | succ t ih =>
    refine continuous_pi (fun v => ?_)
    by_cases h : (ω (t, v)).1 = true
    · have : (fun x : Config k R => run x ω (t + 1) v) = fun _ => (ω (t, v)).2 := by
        funext x
        rw [run_succ, if_pos h]
      rw [this]
      exact continuous_const
    · have : (fun x : Config k R => run x ω (t + 1) v) =
          fun x => quorumRule k R (run x ω t) v := by
        funext x
        rw [run_succ, if_neg h]
      rw [this]
      exact (continuous_quorumRule_apply v).comp ih

/-! ## The operator `Φ` and the integral form of the mixture formula -/

/-- Section 2.2: `Φf(x) = E_x f(X_1)`. -/
def Phi (k : ℕ) (R : WangSet) (ε : ℝ) (f : Config k R → ℝ) (x : Config k R) : ℝ :=
  ∫ y, f y ∂(law k R ε (Measure.dirac x) 1)

theorem integral_law_dirac {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (f : Config k R →ᵇ ℝ)
    (x : Config k R) (t : ℕ) :
    ∫ y, f y ∂(law k R ε (Measure.dirac x) t) = ∫ ω, f (run x ω t) ∂(noiseLaw k R ε) := by
  have hm : Measurable (fun ω : Noise k R => run x ω t) :=
    (measurable_run t).comp measurable_prodMk_left
  rw [law_dirac h0 h1, integral_map hm.aemeasurable f.continuous.aestronglyMeasurable]

/-- `∫ f d(μΦ^t) = ∫ (∫ f d(δ_x Φ^t)) dμ(x)` for bounded continuous `f`. -/
theorem integral_law {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure (Config k R))
    [IsProbabilityMeasure μ] (t : ℕ) (f : Config k R →ᵇ ℝ) :
    ∫ y, f y ∂(law k R ε μ t) = ∫ x, (∫ y, f y ∂(law k R ε (Measure.dirac x) t)) ∂μ := by
  haveI := isProbabilityMeasure_noiseLaw (k := k) (R := R) h0 h1
  have hm := measurable_run (k := k) (R := R) t
  rw [show law k R ε μ t = (μ.prod (noiseLaw k R ε)).map (fun p => run p.1 p.2 t) from rfl,
    integral_map hm.aemeasurable f.continuous.aestronglyMeasurable, integral_prod]
  · congr 1
    funext x
    rw [integral_law_dirac h0 h1]
  · refine Integrable.mono' (integrable_const ‖f‖)
      (f.continuous.measurable.comp hm).aestronglyMeasurable
      (Eventually.of_forall (fun p => f.norm_coe_le_norm _))

/-- **`set:feller`**, first assertion: `Φf` is continuous for every continuous `f : Ω → ℝ`. -/
theorem continuous_Phi {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (f : Config k R → ℝ)
    (hf : Continuous f) : Continuous (Phi k R ε f) := by
  haveI := isProbabilityMeasure_noiseLaw (k := k) (R := R) h0 h1
  let g : Config k R →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩
  have hPhi : Phi k R ε f = fun x => ∫ ω, g (run x ω 1) ∂(noiseLaw k R ε) := by
    funext x
    exact integral_law_dirac h0 h1 g x 1
  rw [hPhi]
  refine continuous_of_dominated (bound := fun _ => ‖g‖) (fun x => ?_)
    (fun x => Eventually.of_forall (fun ω => g.norm_coe_le_norm _)) (integrable_const _)
    (Eventually.of_forall (fun ω => g.continuous.comp (continuous_run ω 1)))
  exact (g.continuous.measurable.comp
    ((measurable_run 1).comp measurable_prodMk_left)).aestronglyMeasurable

/-- `Φf` as a bounded continuous function. -/
def PhiBCF {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (f : Config k R →ᵇ ℝ) : Config k R →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨Phi k R ε f, continuous_Phi h0 h1 f f.continuous⟩

/-- `(μΦ)(f) = μ(Φf)`, and with the Markov property `(μΦ^t)(Φf) = (μΦ^{t+1})(f)`. -/
theorem integral_Phi_law {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure (Config k R))
    [IsProbabilityMeasure μ] (t : ℕ) (f : Config k R →ᵇ ℝ) :
    ∫ x, Phi k R ε f x ∂(law k R ε μ t) = ∫ y, f y ∂(law k R ε μ (t + 1)) := by
  haveI := isProbabilityMeasure_law h0 h1 μ t
  rw [law_succ h0 h1 t μ, integral_law h0 h1 (law k R ε μ t) 1 f]
  rfl

/-! ## Cesàro averages and invariant measures (`set:feller`) -/

/-- `set:feller`: the averages `μ̄_n = (1/n) Σ_{t=0}^{n-1} μΦ^t`. -/
def cesaro (k : ℕ) (R : WangSet) (ε : ℝ) (μ : Measure (Config k R)) (n : ℕ) :
    Measure (Config k R) :=
  (n : ℝ≥0∞)⁻¹ • ∑ t ∈ Finset.range n, law k R ε μ t

theorem isProbabilityMeasure_cesaro {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure (Config k R))
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n) : IsProbabilityMeasure (cesaro k R ε μ n) := by
  constructor
  have : ∀ t, law k R ε μ t Set.univ = 1 := fun t =>
    (isProbabilityMeasure_law h0 h1 μ t).measure_univ
  simp only [cesaro, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, this,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (show n ≠ 0 by omega)) (by simp)

theorem integral_cesaro {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure (Config k R))
    [IsProbabilityMeasure μ] (n : ℕ) (f : Config k R →ᵇ ℝ) :
    ∫ y, f y ∂(cesaro k R ε μ n) = (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, ∫ y, f y ∂(law k R ε μ t) := by
  unfold cesaro
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [ENNReal.toReal_inv]
  · intro t _
    haveI := isProbabilityMeasure_law h0 h1 μ t
    exact f.integrable _

/-- **`set:feller`**, last assertion: every weak limit of the averages along `n_m → ∞` is
invariant. -/
theorem isInvariant_of_cesaro_limit {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure (Config k R))
    [IsProbabilityMeasure μ] {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) (π : Measure (Config k R))
    [IsProbabilityMeasure π] (hπ : WeakTendsto (fun m => cesaro k R ε μ (n m)) π) :
    IsInvariant k R ε π := by
  haveI := isProbabilityMeasure_law h0 h1 π 1
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  set g := PhiBCF h0 h1 f with hg
  have hgx : ∀ x, g x = Phi k R ε f x := fun _ => rfl
  -- `∫ f d(πΦ) = ∫ Φf dπ`
  have hlhs : ∫ y, f y ∂(law k R ε π 1) = ∫ x, g x ∂π := by
    rw [integral_law h0 h1 π 1 f]
    rfl
  rw [hlhs]
  -- along the averages, `∫ Φf - ∫ f = (∫ f d(μΦ^N) - ∫ f dμ) / N → 0`
  have hdiff : Tendsto (fun m => ∫ x, g x ∂(cesaro k R ε μ (n m)) -
      ∫ x, f x ∂(cesaro k R ε μ (n m))) atTop (𝓝 0) := by
    have hbound : ∀ N : ℕ, 1 ≤ N → |∫ x, g x ∂(cesaro k R ε μ N) -
        ∫ x, f x ∂(cesaro k R ε μ N)| ≤ 2 * ‖f‖ / N := by
      intro N hN
      rw [integral_cesaro h0 h1, integral_cesaro h0 h1]
      have htel : ∑ t ∈ Finset.range N, ∫ x, g x ∂(law k R ε μ t) -
          ∑ t ∈ Finset.range N, ∫ x, f x ∂(law k R ε μ t) =
          ∫ x, f x ∂(law k R ε μ N) - ∫ x, f x ∂(law k R ε μ 0) := by
        rw [← Finset.sum_sub_distrib]
        simp only [hgx, integral_Phi_law h0 h1]
        exact Finset.sum_range_sub (fun t => ∫ x, f x ∂(law k R ε μ t)) N
      rw [← mul_sub, htel, abs_mul, abs_inv, Nat.abs_cast, ← div_eq_inv_mul]
      gcongr
      haveI := isProbabilityMeasure_law h0 h1 μ N
      haveI := isProbabilityMeasure_law h0 h1 μ 0
      have b1 := f.norm_integral_le_norm (law k R ε μ N)
      have b2 := f.norm_integral_le_norm (law k R ε μ 0)
      rw [Real.norm_eq_abs] at b1 b2
      calc |∫ x, f x ∂(law k R ε μ N) - ∫ x, f x ∂(law k R ε μ 0)|
          ≤ |∫ x, f x ∂(law k R ε μ N)| + |∫ x, f x ∂(law k R ε μ 0)| := abs_sub _ _
        _ ≤ 2 * ‖f‖ := by linarith
    have hlim : Tendsto (fun m => 2 * ‖f‖ / (n m : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖f‖)).comp hn
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hn.eventually_ge_atTop 1] with m hm
    rw [Real.norm_eq_abs]
    exact hbound (n m) hm
  have hlim := (hπ g).sub (hπ f)
  have := tendsto_nhds_unique hlim hdiff
  linarith

/-- **`set:feller`**, existence: for every `μ` and every `n_m → ∞`, the averages have a weak limit
along a subsequence; the limit is a probability measure. -/
theorem exists_cesaro_limit {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure (Config k R))
    [IsProbabilityMeasure μ] {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ π : Measure (Config k R), IsProbabilityMeasure π ∧
      WeakTendsto (fun m => cesaro k R ε μ (n (φ m))) π := by
  classical
  let ν : ℕ → ProbabilityMeasure (Config k R) := fun m =>
    if h : 1 ≤ n m then ⟨cesaro k R ε μ (n m), isProbabilityMeasure_cesaro h0 h1 μ h⟩
    else ⟨μ, inferInstance⟩
  obtain ⟨π, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ν) (fun _ => Set.mem_univ _)
  refine ⟨φ, hφ, π, inferInstance, fun f => ?_⟩
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) f
  refine h.congr' ?_
  filter_upwards [(hn.comp hφ.tendsto_atTop).eventually_ge_atTop 1] with m hm
  simp only [Function.comp_apply] at hm
  have hν : ν (φ m) = (⟨cesaro k R ε μ (n (φ m)),
      isProbabilityMeasure_cesaro h0 h1 μ hm⟩ : ProbabilityMeasure (Config k R)) :=
    dite_eq_left hm
  simp only [Function.comp_apply, hν, ProbabilityMeasure.coe_mk]

/-- **`set:feller`**: an invariant probability measure exists. -/
theorem exists_invariant {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∃ π : Measure (Config k R), IsProbabilityMeasure π ∧ IsInvariant k R ε π := by
  obtain ⟨φ, hφ, π, hπ, hlim⟩ := exists_cesaro_limit (k := k) (R := R) h0 h1
    (Measure.dirac (fun _ => Sym.bot)) (n := id) tendsto_id
  exact ⟨π, hπ, isInvariant_of_cesaro_limit h0 h1 _ (tendsto_id.comp hφ.tendsto_atTop) π hlim⟩

/-! ## Weak convergence is convergence on cylinders -/

/-- The configuration equal to `z` on the window `W` and to `⊥` elsewhere. -/
def extOf (W : Finset (Site k)) (z : W → Sym R) : Config k R :=
  fun w => if h : w ∈ W then z ⟨w, h⟩ else .bot

/-- Compactness of `Ω`: a continuous `f` varies by less than `δ` between configurations that agree
on some finite window. -/
theorem exists_window_approx (f : Config k R → ℝ) (hf : Continuous f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ W : Finset (Site k), ∀ y y' : Config k R, (∀ w ∈ W, y w = y' w) → |f y - f y'| < δ := by
  classical
  have hloc : ∀ x : Config k R, ∃ W : Finset (Site k),
      ∀ y : Config k R, (∀ w ∈ W, y w = x w) → |f y - f x| < δ / 2 := by
    intro x
    have hU : IsOpen {y : Config k R | |f y - f x| < δ / 2} :=
      isOpen_lt (continuous_abs.comp (hf.sub continuous_const)) continuous_const
    obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU x (by simp; linarith)
    refine ⟨I, fun y hy => hsub ?_⟩
    intro a ha
    rw [hy a ha]
    exact (hu a ha).2
  choose W hW using hloc
  let U : Config k R → Set (Config k R) := fun x => {y | ∀ w ∈ W x, y w = x w}
  have hUn : ∀ x, U x ∈ 𝓝 x := by
    intro x
    refine IsOpen.mem_nhds ?_ (fun w _ => rfl)
    have : U x = ⋂ w ∈ W x, (fun y : Config k R => y w) ⁻¹' {x w} := by
      ext y
      simp [U]
    rw [this]
    exact isOpen_biInter_finset (fun w _ => (isOpen_discrete _).preimage (continuous_apply w))
  obtain ⟨T, hT⟩ := CompactSpace.elim_nhds_subcover U hUn
  refine ⟨T.biUnion W, fun y y' hyy' => ?_⟩
  have hy : y ∈ ⋃ x ∈ T, U x := by
    rw [hT]
    trivial
  obtain ⟨x, hxT, hyx⟩ := Set.mem_iUnion₂.mp hy
  have hy'x : ∀ w ∈ W x, y' w = x w := fun w hw =>
    (hyy' w (Finset.mem_biUnion.mpr ⟨x, hxT, hw⟩)).symm.trans (hyx w hw)
  have h1 := hW x y hyx
  have h2 := hW x y' hy'x
  calc |f y - f y'| = |(f y - f x) - (f y' - f x)| := by ring_nf
    _ ≤ |f y - f x| + |f y' - f x| := abs_sub _ _
    _ < δ / 2 + δ / 2 := add_lt_add h1 h2
    _ = δ := by ring

/-- The integral of a function of the window `W` is a finite sum over cylinders. -/
theorem integral_window (W : Finset (Site k)) (F : (W → Sym R) → ℝ) (ν : Measure (Config k R))
    [IsFiniteMeasure ν] :
    ∫ y, F (fun w : W => y w.1) ∂ν = ∑ z : W → Sym R, (ν (cyl W {z})).toReal * F z := by
  classical
  have hr : Measurable (fun y : Config k R => fun w : W => y w.1) :=
    Measurable.of_eval (fun w => measurable_pi_apply w.1)
  rw [← integral_map hr.aemeasurable (measurable_of_countable F).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [smul_eq_mul, measureReal_def, Measure.map_apply hr (measurableSet_singleton z)]
  rfl

/-- The paragraph after `set:def-ergodic` (⇐): for probability measures, convergence on every
cylinder implies weak convergence. -/
theorem weakTendsto_of_cyl (μs : ℕ → Measure (Config k R)) [∀ t, IsProbabilityMeasure (μs t)]
    (π : Measure (Config k R)) [IsProbabilityMeasure π]
    (h : ∀ (O : Finset (Site k)) (E : Set (O → Sym R)),
      Tendsto (fun t => (μs t (cyl O E)).toReal) atTop (𝓝 (π (cyl O E)).toReal)) :
    WeakTendsto μs π := by
  classical
  intro f
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨W, hW⟩ := exists_window_approx f f.continuous (δ := δ / 4) (by positivity)
  let F : (W → Sym R) → ℝ := fun z => f (extOf W z)
  let g : Config k R →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun y => F (fun w : W => y w.1), continuous_of_local W _ (fun y y' hyy' => by
      simp only [F]
      congr 2
      funext w
      exact hyy' w.1 w.2)⟩
  have hgf : ∀ y, |f y - g y| < δ / 4 := by
    intro y
    refine hW y _ (fun w hw => ?_)
    simp [extOf, hw]
  have happrox : ∀ ν : Measure (Config k R), IsProbabilityMeasure ν →
      |∫ y, f y ∂ν - ∫ y, g y ∂ν| ≤ δ / 4 := by
    intro ν _
    rw [← integral_sub (f.integrable ν) (g.integrable ν)]
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun y => f y - g y) (C := δ / 4)
      (Eventually.of_forall (fun y => (hgf y).le))
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
  have hconv : Tendsto (fun t => ∫ y, g y ∂(μs t)) atTop (𝓝 (∫ y, g y ∂π)) := by
    have e : ∀ ν : Measure (Config k R), IsFiniteMeasure ν →
        ∫ y, g y ∂ν = ∑ z : W → Sym R, (ν (cyl W {z})).toReal * F z :=
      fun ν _ => integral_window W F ν
    simp only [e _ inferInstance]
    exact tendsto_finsetSum _ (fun z _ => (h W {z}).mul_const _)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv (δ / 4) (by positivity)
  refine ⟨N, fun t ht => ?_⟩
  have h2 := hN t ht
  rw [Real.dist_eq] at h2 ⊢
  have a1 := happrox (μs t) inferInstance
  have a2 := happrox π inferInstance
  calc |∫ y, f y ∂(μs t) - ∫ y, f y ∂π|
      ≤ |∫ y, f y ∂(μs t) - ∫ y, g y ∂(μs t)| + |∫ y, g y ∂(μs t) - ∫ y, g y ∂π| +
          |∫ y, g y ∂π - ∫ y, f y ∂π| := by
        have := abs_sub_le (∫ y, f y ∂(μs t)) (∫ y, g y ∂(μs t)) (∫ y, f y ∂π)
        have := abs_sub_le (∫ y, g y ∂(μs t)) (∫ y, g y ∂π) (∫ y, f y ∂π)
        linarith
    _ < δ := by
        rw [abs_sub_comm (∫ y, g y ∂π)]
        linarith

/-- The paragraph after `set:def-ergodic`: for probability measures, `μ_t → π` weakly if and only
if `μ_t(cyl O ℰ) → π(cyl O ℰ)` for every window `O` and every `ℰ ⊆ 𝒜_R^O`. -/
theorem weakTendsto_iff_cyl (μs : ℕ → Measure (Config k R)) [∀ t, IsProbabilityMeasure (μs t)]
    (π : Measure (Config k R)) [IsProbabilityMeasure π] :
    WeakTendsto μs π ↔ ∀ (O : Finset (Site k)) (E : Set (O → Sym R)),
      Tendsto (fun t => (μs t (cyl O E)).toReal) atTop (𝓝 (π (cyl O E)).toReal) := by
  refine ⟨fun h O E => ?_, weakTendsto_of_cyl μs π⟩
  have := h (cylIndicator O E)
  simpa only [integral_cylIndicator] using this

/-- The paragraph after `set:def-ergodic`: for probability measures, `μ_t → π` weakly if and only
if `dtv(μ_t|_O, π|_O) → 0` for every window `O`. -/
theorem weakTendsto_iff_dtv (μs : ℕ → Measure (Config k R)) [∀ t, IsProbabilityMeasure (μs t)]
    (π : Measure (Config k R)) [IsProbabilityMeasure π] :
    WeakTendsto μs π ↔ ∀ O : Finset (Site k), Tendsto (fun t => dtv O (μs t) π) atTop (𝓝 0) := by
  classical
  rw [weakTendsto_iff_cyl]
  constructor
  · intro h O
    have hsum : Tendsto (fun t => ∑ E : Set (O → Sym R),
        |(μs t (cyl O E)).toReal - (π (cyl O E)).toReal|) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Set (O → Sym R)))
        (fun E _ => ((h O E).sub_const (π (cyl O E)).toReal).abs)
      simpa using this
    refine squeeze_zero (fun t => dtv_nonneg _ _ _) (fun t => dtv_le_of (fun E => ?_)) hsum
    exact Finset.single_le_sum (f := fun E : Set (O → Sym R) =>
      |(μs t (cyl O E)).toReal - (π (cyl O E)).toReal|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ E)
  · intro h O E
    have h' : Tendsto (fun t => |(μs t (cyl O E)).toReal - (π (cyl O E)).toReal|) atTop (𝓝 0) :=
      squeeze_zero (fun t => abs_nonneg _) (fun t => abs_le_dtv O _ _ E) (h O)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using h'

end FNE

end
