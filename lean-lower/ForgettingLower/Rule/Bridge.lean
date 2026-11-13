/- Actual dimension-four automaton, decoded updates and complete histories. -/
import ForgettingLower.Rule.Local
import ForgettingLower.Rule.Coordinates
import UncomputableNoiseDiagram.Rule.CA
import UncomputableNoiseDiagram.PCA.Attraction

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace FLD.Rule

open FLD.Geometry (ISite siteEquiv siteEquiv_site siteEquiv_symm site_zero symm_shift site_add)
open FNE (Plane WangSet)

variable {R : WangSet}

/-! ## S1: transport of the frozen checker and quorum -/

theorem check_translate (y : UND.Site 4 → Letter R) (a v : UND.Site 4) :
    check (fun z => y (a + z)) v = check y (a + v) := by
  unfold check Keeps
  simp only [add_assoc]

theorem natMap_translate (y : UND.Site 4 → Letter R) (a : UND.Site 4) :
    natMap R (fun z => y (a + z)) 0 = natMap R y a := by
  have hv : ∀ s, votes (fun z => y (a + z)) 0 s = votes y a s := by
    intro s
    unfold votes
    simp only [zero_add, check_translate]
  unfold natMap
  simp only [hv]

/-- **`natMap` is `GI` transported** along `ℤ⁴ ≅ ℤ² × ℤ²`. -/
theorem natMap_eq (x : UND.Site 4 → Letter R) (v : UND.Site 4) :
    natMap R x v = GI (fun w => x (siteEquiv.symm w)) (siteEquiv v) := by
  have hk : ∀ (o : Fin 2 → ℤ) (c : R), Keeps x (v + site 0 o) c ↔
      KeepsI (fun u => x (siteEquiv.symm (u, (siteEquiv v).2 + o))) (siteEquiv v).1 c := by
    intro o c
    have e : ∀ γ : Plane, x (siteEquiv.symm ((siteEquiv v).1 + γ, (siteEquiv v).2 + o)) =
        x (v + site 0 o + site γ 0) := fun γ => by rw [symm_shift]
    have e0 : x (siteEquiv.symm ((siteEquiv v).1, (siteEquiv v).2 + o)) = x (v + site 0 o) := by
      have := e 0
      rw [add_zero] at this
      rw [this, site_zero, add_zero]
    unfold Keeps KeepsI FNR.Rule.KeepsI
    simp only
    rw [e0, e, e, e, e]
  have hc : ∀ (o : Fin 2 → ℤ) (s : R), check x (v + site 0 o) = some s ↔
      chkI (fun u => x (siteEquiv.symm (u, (siteEquiv v).2 + o))) (siteEquiv v).1 = some s := by
    intro o s
    rw [chkI_eq_some]
    unfold check
    split_ifs with h
    · obtain ⟨c, hc⟩ := h
      constructor
      · intro e
        have e' : some c = some s := hc.1.symm.trans e
        rw [← Option.some_injective _ e']
        exact (hk o c).1 hc
      · intro hks
        exact ((hk o s).2 hks).1
    · exact ⟨fun e => absurd e (by simp), fun hks => absurd ⟨s, (hk o s).2 hks⟩ h⟩
  have hv : ∀ s, votes x v s = votesI (fun w => x (siteEquiv.symm w)) (siteEquiv v) s := by
    intro s
    unfold votes votesI
    congr 1
    refine Finset.filter_congr fun π _ => ?_
    exact hc _ s
  unfold natMap GI
  simp only [hv]

/-- `natMap R x v` reads `x` only on `v + Γ × S`. -/
theorem natMap_local {x x' : UND.Site 4 → Letter R} {v : UND.Site 4}
    (h : ∀ z ∈ natNbhd, x (v + z) = x' (v + z)) : natMap R x v = natMap R x' v := by
  rw [natMap_eq, natMap_eq]
  refine GI_congr fun γ hγ π => ?_
  show x (siteEquiv.symm _) = x' (siteEquiv.symm _)
  rw [symm_shift, add_assoc, site_add]
  refine h _ (Finset.mem_image.2 ⟨(γ, π), Finset.mem_product.2 ⟨hγ, Finset.mem_univ _⟩, ?_⟩)
  rfl

/-! ## S2: decoding -/

/-- A configuration of `natCA R`, decoded to `ℤ² × ℤ² → A_R`. -/
def dec (x : (natCA R).Config) : ISite → Letter R :=
  fun w => (letterEquiv R).symm (x (siteEquiv.symm w))

/-- **The global map of `natCA R` is `G_R`.** -/
theorem natCA_apply (x : (natCA R).Config) (w4 : UND.Site 4) :
    (natCA R).apply x w4 = letterEquiv R (GI (dec x) (siteEquiv w4)) := by
  have e1 : (natCA R).apply x w4 = letterEquiv R (natMap R (fun z =>
      if h : z ∈ natNbhd then (letterEquiv R).symm (x (w4 + z)) else none) 0) := rfl
  have e2 : natMap R (fun z =>
      if h : z ∈ natNbhd then (letterEquiv R).symm (x (w4 + z)) else none) 0 =
      natMap R (fun z => (letterEquiv R).symm (x (w4 + z))) 0 :=
    natMap_local fun z hz => by rw [zero_add, dite_eq_left hz]
  rw [e1, e2, natMap_translate (fun z => (letterEquiv R).symm (x z)) w4, natMap_eq]
  rfl

/-- One noisy update, decoded. -/
theorem dec_update (e : UND.Site 4 → Bool × (natCA R).Sym) (x : (natCA R).Config) :
    dec ((natCA R).update e x) = fun w =>
      if (e (siteEquiv.symm w)).1 then (letterEquiv R).symm (e (siteEquiv.symm w)).2
      else GI (dec x) w := by
  funext w
  unfold dec UND.CA.update
  split_ifs with h
  · rfl
  · rw [natCA_apply, AddEquiv.apply_symm_apply, Equiv.symm_apply_apply]
    rfl

theorem dec_inj {x y : (natCA R).Config} (h : dec x = dec y) : x = y := by
  funext v
  have := congrFun h (siteEquiv v)
  unfold dec at this
  rw [AddEquiv.symm_apply_apply] at this
  exact (letterEquiv R).symm.injective this

/-! ## S3: trajectories -/

/-- **A complete trajectory, decoded, is a trajectory of `G_R`** with the replacement flags of its
noise, from every time `s`. -/
theorem isTraj_of_complete {ω : (natCA R).Noise₂} {X : ℤ → (natCA R).Config}
    (hX : (natCA R).IsComplete ω X) (s : ℤ) :
    IsTraj s (fun t => dec (X t)) (FLD.Geometry.flagsOf ω) := by
  intro t w _ hE
  have h := hX (t - 1)
  rw [sub_add_cancel] at h
  show dec (X t) w = GI (dec (X (t - 1))) w
  rw [h, dec_update]
  exact ite_eq_right hE

/-- At a flag, two complete trajectories with the same noise agree. -/
theorem complete_flag_eq {ω : (natCA R).Noise₂} {X Y : ℤ → (natCA R).Config}
    (hX : (natCA R).IsComplete ω X) (hY : (natCA R).IsComplete ω Y) {t : ℤ} {w : ISite}
    (hE : FLD.Geometry.flagsOf ω t w) : dec (X t) w = dec (Y t) w := by
  have h1 := hX (t - 1)
  have h2 := hY (t - 1)
  rw [sub_add_cancel] at h1 h2
  have hE' : (ω (t, siteEquiv.symm w)).1 = true := hE
  rw [h1, h2, dec_update, dec_update]
  simp only [hE', ↓reduceIte]

/-- The forward process from time `0` (`Ψ_{0,n}`, `UND.CA.flow`), decoded, indexed by `ℤ`. -/
def flowTraj (ω : (natCA R).Noise₂) (x : (natCA R).Config) : ℤ → ISite → Letter R :=
  fun t => dec ((natCA R).flow ω 0 t.toNat x)

/-- **The forward process from time `0` is a trajectory of `G_R` from time `0`** with the flags of
the two-sided noise. -/
theorem isTraj_flow (ω : (natCA R).Noise₂) (x : (natCA R).Config) :
    IsTraj 0 (flowTraj ω x) (FLD.Geometry.flagsOf ω) := by
  intro t w ht hE
  obtain ⟨n, hn⟩ : ∃ n : ℕ, t = n + 1 := ⟨(t - 1).toNat, by omega⟩
  subst hn
  unfold flowTraj
  rw [show ((n : ℤ) + 1).toNat = n + 1 by omega, show ((n : ℤ) + 1 - 1).toNat = n by omega]
  show dec ((natCA R).update (fun w => ω (0 + (n : ℤ) + 1, w)) ((natCA R).flow ω 0 n x)) w = _
  rw [dec_update]
  refine ite_eq_right ?_
  rw [zero_add]
  exact hE

theorem flowTraj_zero (ω : (natCA R).Noise₂) (x : (natCA R).Config) :
    flowTraj ω x 0 = dec x := rfl

theorem flowTraj_nat (ω : (natCA R).Noise₂) (x : (natCA R).Config) (n : ℕ) :
    flowTraj ω x n = dec ((natCA R).flow ω 0 n x) := by
  unfold flowTraj
  rw [Int.toNat_natCast]

end FLD.Rule
