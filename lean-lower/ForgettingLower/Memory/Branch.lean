/- Tiling branch for the actual dimension-four rule: branch. -/
import ForgettingLower.Memory.Cover
import ForgettingLower.Forget.Roots
import UncomputableNoiseDiagram.PCA.Attraction

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace FLD.Memory

open FLD.Geometry FLD.Rule
open FNE (Plane WangSet)

variable {R : WangSet}

/-- The start `ξ_θ(u, P) = θ(u)` as a configuration of `natCA R`. -/
def cloneCfg (θ : Plane → R) : (natCA R).Config := fun v => letterEquiv R (some (θ (v 0, v 1)))

/-- The all-blank start as a configuration of `natCA R`. -/
def blankCfg : (natCA R).Config := fun _ => letterEquiv R none

theorem dec_cloneCfg (θ : Plane → R) : dec (cloneCfg θ) = clone θ := by
  funext w
  show (letterEquiv R).symm (letterEquiv R (some (θ ((siteEquiv.symm w) 0,
    (siteEquiv.symm w) 1)))) = some (θ w.1)
  rw [Equiv.symm_apply_apply]
  rfl

theorem dec_blankCfg : dec (blankCfg (R := R)) = fun _ => none := by
  funext w
  exact Equiv.symm_apply_apply _ _

theorem dec_siteEquiv (x : (natCA R).Config) (v : UND.Site 4) :
    dec x (siteEquiv v) = (letterEquiv R).symm (x v) := by
  unfold dec
  rw [AddEquiv.symm_apply_apply]

/-- **A bad event covered by `𝓜` has probability at most `1/4` at every time.** -/
theorem law_bad_le (x : (natCA R).Config) {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ eps0) (n : ℕ)
    (v : UND.Site 4) (S : Set (natCA R).Sym)
    (hcov : ∀ ω : (natCA R).Noise₂, (natCA R).flow ω 0 n x v ∈ S →
      marked (flagsOf ω) n (siteEquiv v)) :
    (natCA R).law ε (Measure.dirac x) n {y | y v ∈ S} ≤ 4⁻¹ := by
  have h1 : ε ≤ 1 := hε.trans Const.eps0_le_one
  have hmr : Measurable (fun ω : (natCA R).Noise => (natCA R).run x ω n) :=
    ((natCA R).measurable_run n).comp measurable_prodMk_left
  have hS : MeasurableSet {y : (natCA R).Config | y v ∈ S} :=
    (measurable_pi_apply v) (Set.toFinite S).measurableSet
  rw [(natCA R).law_dirac h0 h1, Measure.map_apply hmr hS,
    ← (natCA R).noiseLaw₂_map_tau h0 h1 0, Measure.map_apply ((natCA R).measurable_tau 0) (hmr hS)]
  refine (measure_mono fun ω hω => ?_).trans
    (Forget.root_bound (natCA R) h0 hε (siteEquiv v) n)
  have hω' : (natCA R).run x ((natCA R).tau 0 ω) n v ∈ S := hω
  rw [← (natCA R).flow_eq_run] at hω'
  exact hcov ω hω'

/-- **The memory branch of Theorem 12.5**: if `R` tiles the plane, `G_R` is not ergodic at any
`0 ≤ ε ≤ e₀`. -/
theorem memory_branch (hR : TilesPlane R) {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ eps0) :
    ¬ (natCA R).IsErgodic ε := by
  obtain ⟨θ0, hθR, hEm, hNm⟩ := hR
  let θ : Plane → R := fun u => ⟨θ0 u, hθR u⟩
  have hθ : Legal θ := fun u => ⟨hEm u, hNm u⟩
  have h1 : ε ≤ 1 := hε.trans Const.eps0_le_one
  let c : (natCA R).Sym := letterEquiv R (some (θ 0))
  have hz : clone θ (siteEquiv 0) = some (θ 0) := by simp [clone, map_zero]
  have hO : (0 : UND.Site 4) ∈ ({0} : Finset (UND.Site 4)) := Finset.mem_singleton_self _
  -- the clone: a wrong letter at `0` is marked
  have hclone : ∀ t : ℕ, (natCA R).law ε (Measure.dirac (cloneCfg θ)) t
      {y | y 0 ∈ ({c}ᶜ : Set (natCA R).Sym)} ≤ 4⁻¹ := fun t =>
    law_bad_le (cloneCfg θ) h0 hε t 0 {c}ᶜ fun ω hω => by
      refine marked_of_markedFrom (clone_cover hθ (isTraj_flow ω (cloneCfg θ))
        (by rw [flowTraj_zero, dec_cloneCfg]) t (siteEquiv 0) ?_)
      rw [flowTraj_nat, dec_siteEquiv, hz]
      intro heq
      exact hω ((Equiv.symm_apply_eq _).1 heq)
  -- blank: a live letter at `0` is marked
  have hblank : ∀ t : ℕ, (natCA R).law ε (Measure.dirac blankCfg) t
      {y | y 0 ∈ ({c} : Set (natCA R).Sym)} ≤ 4⁻¹ := fun t =>
    law_bad_le blankCfg h0 hε t 0 {c} fun ω hω => by
      refine marked_of_markedFrom (blank_cover (isTraj_flow ω blankCfg)
        (by rw [flowTraj_zero, dec_blankCfg]) t (siteEquiv 0) ?_)
      rw [flowTraj_nat, dec_siteEquiv, Set.mem_singleton_iff.1 hω, Equiv.symm_apply_apply]
      exact Option.some_ne_none _
  have e1 : (natCA R).cyl {0} {f | f ⟨0, hO⟩ = c} = {y | y 0 ∈ ({c} : Set (natCA R).Sym)} := by
    ext y
    simp [UND.CA.cyl]
  have e2 : ((natCA R).cyl {0} {f | f ⟨0, hO⟩ = c})ᶜ =
      {y | y 0 ∈ ({c}ᶜ : Set (natCA R).Sym)} := by
    rw [e1]
    ext y
    simp
  refine (natCA R).not_ergodic_of_memoryFrom (μ := Measure.dirac (cloneCfg θ))
    (μ' := Measure.dirac blankCfg) ⟨{0}, {f | f ⟨0, hO⟩ = c}, 1 / 2, by norm_num, fun t => ?_⟩
  have hcm : MeasurableSet ((natCA R).cyl {0} {f | f ⟨0, hO⟩ = c}) :=
    (natCA R).measurableSet_cyl _ _
  have hA : ((natCA R).law ε (Measure.dirac blankCfg) t
      ((natCA R).cyl {0} {f | f ⟨0, hO⟩ = c})).toReal ≤ 1 / 4 := by
    rw [e1]
    have := ENNReal.toReal_mono (by simp) (hblank t)
    simpa using this
  have hB : 3 / 4 ≤ ((natCA R).law ε (Measure.dirac (cloneCfg θ)) t
      ((natCA R).cyl {0} {f | f ⟨0, hO⟩ = c})).toReal := by
    have := (natCA R).isProbabilityMeasure_law h0 h1 (Measure.dirac (cloneCfg θ)) t
    rw [← compl_compl ((natCA R).cyl {0} {f | f ⟨0, hO⟩ = c}), prob_compl_eq_one_sub hcm.compl,
      e2, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
    have := ENNReal.toReal_mono (by simp) (hclone t)
    simp only [ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at this ⊢
    linarith
  linarith

end FLD.Memory
