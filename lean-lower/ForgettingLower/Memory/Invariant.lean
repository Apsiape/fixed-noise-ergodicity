/- Tiling branch for the actual dimension-four rule: invariant. -/
import ForgettingLower.Memory.Branch
import ForgettingNaturalRule.PCA.Average

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace FLD.Memory

open FLD.Geometry FLD.Rule
open FNE (Plane WangSet)

variable {R : WangSet}

/-- From the clone of a legal `θ`, the blank letter is seen at a site `v` with probability at most
`1/4`, at every time (the errors are covered by `𝓜`). -/
theorem clone_blank_le {θ : Plane → R} (hθ : Legal θ) {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ eps0)
    (t : ℕ) (v : UND.Site 4) :
    (natCA R).law ε (Measure.dirac (cloneCfg θ)) t
      {y | y v ∈ ({letterEquiv R none} : Set (natCA R).Sym)} ≤ 4⁻¹ :=
  law_bad_le (cloneCfg θ) h0 hε t v _ fun ω hω => by
    refine marked_of_markedFrom (clone_cover hθ (isTraj_flow ω (cloneCfg θ))
      (by rw [flowTraj_zero, dec_cloneCfg]) t (siteEquiv v) ?_)
    rw [flowTraj_nat, dec_siteEquiv, Set.mem_singleton_iff.1 hω, Equiv.symm_apply_apply]
    exact (Option.some_ne_none _).symm

/-- From the all-blank start, a live letter is seen at a site `v` with probability at most `1/4`,
at every time. -/
theorem blank_live_le {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ eps0) (t : ℕ) (v : UND.Site 4) :
    (natCA R).law ε (Measure.dirac blankCfg) t
      {y | y v ∈ ({letterEquiv R none}ᶜ : Set (natCA R).Sym)} ≤ 4⁻¹ :=
  law_bad_le blankCfg h0 hε t v _ fun ω hω => by
    refine marked_of_markedFrom (blank_cover (isTraj_flow ω blankCfg)
      (by rw [flowTraj_zero, dec_blankCfg]) t (siteEquiv v) ?_)
    rw [flowTraj_nat, dec_siteEquiv]
    intro heq
    exact hω ((Equiv.symm_apply_eq _).1 heq)

/-- **Theorem 12.5, last clause**: if `R` tiles the plane, `G_R` has two distinct
invariant probability laws at every `0 ≤ ε ≤ e₀`. -/
theorem twoInvariant_of_tiles (hR : TilesPlane R) {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ eps0) :
    HasTwoInvariantLaws (natCA R) ε := by
  obtain ⟨θ0, hθR, hEm, hNm⟩ := hR
  let θ : Plane → R := fun u => ⟨θ0 u, hθR u⟩
  have hθ : Legal θ := fun u => ⟨hEm u, hNm u⟩
  have h1 : ε ≤ 1 := hε.trans Const.eps0_le_one
  have hc : (4 : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  -- the clone: few blanks, at every site
  obtain ⟨π₁, hp₁, hs₁, hb₁⟩ := FNR.Avg.exists_stationary_le (natCA R) h0 h1
    (Measure.dirac (cloneCfg θ)) _ _ hc (fun t v => clone_blank_le hθ h0 hε t v)
  -- blank: few live letters, at every site
  obtain ⟨π₂, hp₂, hs₂, hb₂⟩ := FNR.Avg.exists_stationary_le (natCA R) h0 h1
    (Measure.dirac blankCfg) _ _ hc (fun t v => blank_live_le h0 hε t v)
  refine ⟨π₁, π₂, fun heq => ?_, hp₁, hs₁, hp₂, hs₂⟩
  -- the event `{x(0) = ⊥}` separates them
  have hm := FNR.Avg.measurableSet_site (natCA R) 0 ({letterEquiv R none} : Set (natCA R).Sym)
  have hsum := prob_add_prob_compl (μ := π₂) hm
  have e : {y : (natCA R).Config | y 0 ∈ ({letterEquiv R none} : Set (natCA R).Sym)}ᶜ =
      {y | y 0 ∈ ({letterEquiv R none}ᶜ : Set (natCA R).Sym)} := by
    ext y
    simp
  rw [e] at hsum
  have hA := hb₁ 0
  rw [heq] at hA
  have hB := hb₂ 0
  have hle : (1 : ℝ≥0∞) ≤ 4⁻¹ + 4⁻¹ := hsum ▸ add_le_add hA hB
  have hlt : (4 : ℝ≥0∞)⁻¹ + 4⁻¹ < 1 := by
    have h4 : (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 4) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      simp
    rw [h4, ← ENNReal.ofReal_add (by norm_num) (by norm_num), ENNReal.ofReal_lt_one]
    norm_num
  exact absurd hle (not_le.2 hlt)

end FLD.Memory
