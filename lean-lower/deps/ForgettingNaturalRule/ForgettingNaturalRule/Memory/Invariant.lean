/-
# Two translation-invariant stationary laws on tilers (Theorem D, last clause) (node M5)

Paper (Theorem D): "If `R` tiles, there are two distinct translation-invariant stationary laws."
Section 2, "Fully translation-invariant stationary laws": "first average the Dirac law at `θ` over
larger and larger planar squares … Clone a tiling sampled from `ν` in all transverse coordinates.
Its row law is invariant under all translations of `ℤ⁶`. The kernel commutes with those
translations. All its time marginals and their Cesàro limits are therefore spatially invariant.
Integrating the first bound of (`nw:memorybounds`) over `ν` shows that the live probability at
every site is at least `1 - 2ε`. From the all-blank start it is at most `2ε`. The corresponding
invariant limits are distinguished by the fixed event `{x : x(v) ≠ ⊥}`."

Formalization. The two averages are taken in the other order (`PCA/Average.lean`): the memory
bounds hold at every site and time (Lemma `nw:memory` in the weak form of `Memory/Branch.lean`,
`P(X_t(v) = ⊥) ≤ 1/4` from the clone and `P(Y_t(v) ≠ ⊥) ≤ 1/4` from blank), so the temporal Cesàro
limits from the two Dirac starts are stationary laws with the same one-site bounds at every site
(`Avg.exists_stationary_le`); averaging each along the six coordinate directions gives a
translation-invariant stationary law with the same bounds (`Avg.exists_TI`). The event
`{x : x(0) = ⊥}` has probability at most `1/4` under the first and at least `3/4` under the second.
* `clone_blank_le`, `blank_live_le` (the two memory bounds at every site);
* **`twoTI_of_tiles`**.
-/
import ForgettingNaturalRule.Memory.Branch
import ForgettingNaturalRule.PCA.Average

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace FNR.Memory

open UND.Rule (siteEquiv)
open FNR.Rule
open FNE (Plane WangSet)

variable {R : WangSet}

/-- From the clone of a legal `θ`, the blank letter is seen at a site `v` with probability at most
`1/4`, at every time (the errors are covered by `𝓜`). -/
theorem clone_blank_le {θ : Plane → R} (hθ : Legal θ) {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ epsStar)
    (t : ℕ) (v : UND.Site 6) :
    (natCA R).law ε (Measure.dirac (cloneCfg θ)) t
      {y | y v ∈ ({letterEquiv R none} : Set (natCA R).Sym)} ≤ 4⁻¹ :=
  law_bad_le (cloneCfg θ) h0 hε t v _ fun ω hω => by
    refine marked_of_markedFrom (clone_cover hθ (isTraj_flow ω (cloneCfg θ))
      (by rw [flowTraj_zero, dec_cloneCfg]) t (siteEquiv v) ?_)
    rw [flowTraj_nat, dec_siteEquiv, Set.mem_singleton_iff.1 hω, Equiv.symm_apply_apply]
    exact (Option.some_ne_none _).symm

/-- From the all-blank start, a live letter is seen at a site `v` with probability at most `1/4`,
at every time. -/
theorem blank_live_le {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ epsStar) (t : ℕ) (v : UND.Site 6) :
    (natCA R).law ε (Measure.dirac blankCfg) t
      {y | y v ∈ ({letterEquiv R none}ᶜ : Set (natCA R).Sym)} ≤ 4⁻¹ :=
  law_bad_le blankCfg h0 hε t v _ fun ω hω => by
    refine marked_of_markedFrom (blank_cover (isTraj_flow ω blankCfg)
      (by rw [flowTraj_zero, dec_blankCfg]) t (siteEquiv v) ?_)
    rw [flowTraj_nat, dec_siteEquiv]
    intro heq
    exact hω ((Equiv.symm_apply_eq _).1 heq)

/-- **Theorem D, last clause**: if `R` tiles the plane, `G_R` has two distinct
translation-invariant stationary laws at every `0 ≤ ε ≤ ε_*`. -/
theorem twoTI_of_tiles (hR : TilesPlane R) {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ epsStar) :
    (natCA R).HasTwoTIStationaryLaws ε := by
  obtain ⟨θ0, hθR, hEm, hNm⟩ := hR
  let θ : Plane → R := fun u => ⟨θ0 u, hθR u⟩
  have hθ : Legal θ := fun u => ⟨hEm u, hNm u⟩
  have h1 : ε ≤ 1 := hε.trans Const.epsStar_le_one
  have hc : (4 : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  -- the clone: few blanks, at every site
  obtain ⟨π₁, hp₁, hs₁, hb₁⟩ := Avg.exists_stationary_le (natCA R) h0 h1
    (Measure.dirac (cloneCfg θ)) _ _ hc (fun t v => clone_blank_le hθ h0 hε t v)
  obtain ⟨ν₁, hq₁, hst₁, hti₁, hν₁⟩ := Avg.exists_TI (natCA R) h0 h1 π₁ hs₁ _ _ hc hb₁
  -- blank: few live letters, at every site
  obtain ⟨π₂, hp₂, hs₂, hb₂⟩ := Avg.exists_stationary_le (natCA R) h0 h1
    (Measure.dirac blankCfg) _ _ hc (fun t v => blank_live_le h0 hε t v)
  obtain ⟨ν₂, hq₂, hst₂, hti₂, hν₂⟩ := Avg.exists_TI (natCA R) h0 h1 π₂ hs₂ _ _ hc hb₂
  refine ⟨ν₁, ν₂, fun heq => ?_, hq₁, hst₁, hti₁, hq₂, hst₂, hti₂⟩
  -- the event `{x(0) = ⊥}` separates them
  have hm := Avg.measurableSet_site (natCA R) 0 ({letterEquiv R none} : Set (natCA R).Sym)
  have hsum := prob_add_prob_compl (μ := ν₂) hm
  have e : {y : (natCA R).Config | y 0 ∈ ({letterEquiv R none} : Set (natCA R).Sym)}ᶜ =
      {y | y 0 ∈ ({letterEquiv R none}ᶜ : Set (natCA R).Sym)} := by
    ext y
    simp
  rw [e] at hsum
  have hA := hν₁ 0
  rw [heq] at hA
  have hB := hν₂ 0
  have hle : (1 : ℝ≥0∞) ≤ 4⁻¹ + 4⁻¹ := hsum ▸ add_le_add hA hB
  have hlt : (4 : ℝ≥0∞)⁻¹ + 4⁻¹ < 1 := by
    have h4 : (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 4) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      simp
    rw [h4, ← ENNReal.ofReal_add (by norm_num) (by norm_num), ENNReal.ofReal_lt_one]
    norm_num
  exact absurd hle (not_le.2 hlt)

end FNR.Memory
