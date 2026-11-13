/-
# Section 2.3: memory excludes ergodicity (decision D8: the direct proof)

`set:def-forget` (memory) and `set:memory-nonergodic` in the direct form of decision D8 (BLUEPRINT
Part D): if the process has memory, it is not ergodic. Under ergodicity both
`law (δ_x) t` and `law (δ_{x'}) t` converge weakly to `π`; the indicator of the clopen cylinder
`{y : y|_O ∈ ℰ}` is bounded and continuous, so both probabilities converge to `π(Γ)`, against
the gap `α > 0`. (The paper's statement also produces two invariant measures; that is not needed
for `cor:eight`.)
-/
import FixedNoiseErgodicity.Section2.Process
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

noncomputable section

namespace FNE

open MeasureTheory Filter Topology

variable {k : ℕ} {R : WangSet}

/-- `set:def-ergodic`, paragraph after it: the cylinder `{y : y|_O ∈ ℰ}` of a window `O`. -/
def cyl (O : Finset (Site k)) (E : Set (O → Sym R)) : Set (Config k R) :=
  {y | (fun w : O => y w.1) ∈ E}

theorem continuous_restrictWindow (O : Finset (Site k)) :
    Continuous (fun y : Config k R => fun w : O => y w.1) :=
  continuous_pi (fun w => continuous_apply w.1)

theorem measurableSet_cyl (O : Finset (Site k)) (E : Set (O → Sym R)) :
    MeasurableSet (cyl O E) :=
  (Measurable.of_eval (fun w => measurable_pi_apply w.1)) E.to_countable.measurableSet

/-- The indicator of a cylinder, a bounded continuous function (cylinders are clopen). -/
def cylIndicator (O : Finset (Site k)) (E : Set (O → Sym R)) :
    BoundedContinuousFunction (Config k R) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨(cyl O E).indicator 1, by
      have : (cyl O E).indicator (1 : Config k R → ℝ) =
          E.indicator 1 ∘ (fun y : Config k R => fun w : O => y w.1) := by
        funext y
        exact Set.indicator_comp_right (s := E) (g := (1 : (O → Sym R) → ℝ))
          (fun y : Config k R => fun w : O => y w.1)
      rw [this]
      exact continuous_of_discreteTopology.comp (continuous_restrictWindow O)⟩
    1 (by
      intro y y'
      simp only [ContinuousMap.coe_mk, Set.indicator, Pi.one_apply]
      split_ifs <;> norm_num)

theorem integral_cylIndicator (O : Finset (Site k)) (E : Set (O → Sym R))
    (μ : Measure (Config k R)) :
    ∫ y, cylIndicator O E y ∂μ = (μ (cyl O E)).toReal := by
  have h : (fun y => cylIndicator O E y) = (cyl O E).indicator 1 := rfl
  rw [h, integral_indicator_one (measurableSet_cyl O E), measureReal_def]

/-- `set:def-forget`. The process *has memory*: there are configurations `x, x'`, a window `O`, a
set `ℰ ⊆ 𝒜_R^O` and `α > 0` with `P_x(X_t|_O ∈ ℰ) ≥ P_{x'}(X_t|_O ∈ ℰ) + α` for every `t ≥ 0`. -/
def HasMemory (k : ℕ) (R : WangSet) (ε : ℝ) : Prop :=
  ∃ (x x' : Config k R) (O : Finset (Site k)) (E : Set (O → Sym R)) (α : ℝ), 0 < α ∧
    ∀ t, (law k R ε (Measure.dirac x') t (cyl O E)).toReal + α ≤
      (law k R ε (Measure.dirac x) t (cyl O E)).toReal

/-- **`set:memory-nonergodic`** (direct form, D8). If the process has memory, it is not
ergodic. -/
theorem not_ergodic_of_memory {ε : ℝ} (h : HasMemory k R ε) : ¬ IsErgodic k R ε := by
  rintro ⟨π, -, -, -, hconv⟩
  obtain ⟨x, x', O, E, α, hα, hmem⟩ := h
  have hx := hconv (Measure.dirac x) inferInstance (cylIndicator O E)
  have hx' := hconv (Measure.dirac x') inferInstance (cylIndicator O E)
  simp only [integral_cylIndicator] at hx hx'
  have hd := hx.sub hx'
  rw [sub_self] at hd
  have : α ≤ 0 := ge_of_tendsto' hd (fun t => by linarith [hmem t])
  linarith

/-! ## `set:def-forget`: total variation on windows, `δ_O(t)`, forgetting -/

/-- Paragraph after `set:def-ergodic`: the total variation distance of the marginals on a window
`O`, `dtv(μ|_O, ν|_O) = max_{ℰ ⊆ 𝒜_R^O} |μ|_O(ℰ) - ν|_O(ℰ)|`, where `μ|_O(ℰ) = μ(cyl O ℰ)`. -/
def dtv (O : Finset (Site k)) (μ ν : Measure (Config k R)) : ℝ :=
  ⨆ E : Set (O → Sym R), |(μ (cyl O E)).toReal - (ν (cyl O E)).toReal|

/-- `set:def-forget`. `δ_O(t) = sup_x dtv(Law_x(X_t|_O), Law_⊥(X_t|_O))`. -/
def deltaO (k : ℕ) (R : WangSet) (ε : ℝ) (O : Finset (Site k)) (t : ℕ) : ℝ :=
  ⨆ x : Config k R,
    dtv O (law k R ε (Measure.dirac x) t) (law k R ε (Measure.dirac (fun _ => Sym.bot)) t)

/-- `set:def-forget`. The process *forgets* if `δ_O(t) → 0` as `t → ∞` for every window `O`. -/
def Forgets (k : ℕ) (R : WangSet) (ε : ℝ) : Prop :=
  ∀ O : Finset (Site k), Tendsto (deltaO k R ε O) atTop (𝓝 0)

theorem abs_le_dtv (O : Finset (Site k)) (μ ν : Measure (Config k R)) (E : Set (O → Sym R)) :
    |(μ (cyl O E)).toReal - (ν (cyl O E)).toReal| ≤ dtv O μ ν :=
  le_ciSup (f := fun E : Set (O → Sym R) => |(μ (cyl O E)).toReal - (ν (cyl O E)).toReal|)
    (Set.finite_range _).bddAbove E

theorem dtv_le_of {O : Finset (Site k)} {μ ν : Measure (Config k R)} {c : ℝ}
    (h : ∀ E : Set (O → Sym R), |(μ (cyl O E)).toReal - (ν (cyl O E)).toReal| ≤ c) :
    dtv O μ ν ≤ c :=
  ciSup_le h

theorem dtv_nonneg (O : Finset (Site k)) (μ ν : Measure (Config k R)) : 0 ≤ dtv O μ ν :=
  Real.iSup_nonneg (fun _ => abs_nonneg _)

theorem dtv_comm (O : Finset (Site k)) (μ ν : Measure (Config k R)) : dtv O μ ν = dtv O ν μ := by
  unfold dtv
  congr 1
  funext E
  exact abs_sub_comm _ _

theorem dtv_le_one (O : Finset (Site k)) (μ ν : Measure (Config k R)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : dtv O μ ν ≤ 1 := by
  refine dtv_le_of (fun E => ?_)
  rw [← measureReal_def, ← measureReal_def, abs_sub_le_iff]
  have h1 : μ.real (cyl O E) ≤ 1 := measureReal_le_one
  have h2 : ν.real (cyl O E) ≤ 1 := measureReal_le_one
  have h3 : 0 ≤ μ.real (cyl O E) := measureReal_nonneg
  have h4 : 0 ≤ ν.real (cyl O E) := measureReal_nonneg
  constructor <;> linarith

theorem deltaO_nonneg (ε : ℝ) (O : Finset (Site k)) (t : ℕ) : 0 ≤ deltaO k R ε O t :=
  Real.iSup_nonneg (fun _ => dtv_nonneg _ _ _)

theorem dtv_le_deltaO {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (O : Finset (Site k)) (t : ℕ)
    (x : Config k R) :
    dtv O (law k R ε (Measure.dirac x) t) (law k R ε (Measure.dirac (fun _ => Sym.bot)) t) ≤
      deltaO k R ε O t := by
  refine le_ciSup (f := fun x : Config k R => dtv O (law k R ε (Measure.dirac x) t)
    (law k R ε (Measure.dirac (fun _ => Sym.bot)) t)) ⟨1, ?_⟩ x
  rintro _ ⟨y, rfl⟩
  haveI := isProbabilityMeasure_law h0 h1 (Measure.dirac y) t
  haveI := isProbabilityMeasure_law h0 h1 (Measure.dirac (fun _ : Site k => (Sym.bot : Sym R))) t
  exact dtv_le_one _ _ _

theorem deltaO_le_of {ε : ℝ} {O : Finset (Site k)} {t : ℕ} {c : ℝ}
    (h : ∀ x : Config k R,
      dtv O (law k R ε (Measure.dirac x) t) (law k R ε (Measure.dirac (fun _ => Sym.bot)) t) ≤ c) :
    deltaO k R ε O t ≤ c :=
  ciSup_le h

end FNE

end
