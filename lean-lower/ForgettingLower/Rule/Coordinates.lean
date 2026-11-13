/- The additive identification of the actual Z4 sites with planar/transverse sites. -/
import ForgettingLower.Geometry.Noise

set_option autoImplicit false

namespace FLD.Geometry

/-- Physical coordinates to the product coordinates used by the ordinary graph. -/
def siteEquiv : UND.Site 4 ≃+ ISite where
  toFun v := ((v 0, v 1), fun i => v i.succ.succ)
  invFun := toSite
  left_inv v := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
  right_inv w := by rfl
  map_add' v w := rfl

theorem siteEquiv_site (u : FNE.Plane) (P : Fin 2 → ℤ) :
    siteEquiv (site u P) = (u, P) := rfl

theorem siteEquiv_symm (u : FNE.Plane) (P : Fin 2 → ℤ) :
    siteEquiv.symm (u, P) = site u P := rfl

theorem site_zero : site (0 : FNE.Plane) (0 : Fin 2 → ℤ) = 0 := by
  apply siteEquiv.injective
  rw [siteEquiv_site, map_zero, Prod.mk_zero_zero]

theorem symm_shift (v : UND.Site 4) (γ : FNE.Plane) (o : Fin 2 → ℤ) :
    siteEquiv.symm ((siteEquiv v).1 + γ, (siteEquiv v).2 + o) =
      v + site 0 o + site γ 0 := by
  apply siteEquiv.injective
  rw [AddEquiv.apply_symm_apply, map_add, map_add, siteEquiv_site, siteEquiv_site]
  ext <;> simp [add_comm]

theorem site_add (γ : FNE.Plane) (o : Fin 2 → ℤ) :
    site 0 o + site γ 0 = site γ o := by
  apply siteEquiv.injective
  rw [map_add, siteEquiv_site, siteEquiv_site, siteEquiv_site]
  ext <;> simp

end FLD.Geometry
