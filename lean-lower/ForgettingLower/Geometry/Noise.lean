/- Dimension-four product-site coordinates and fixed deterministic flag events.
The generic product-noise identity is reused; no six-dimensional site map is used. -/
import ForgettingLower.Geometry.Marked
import UncomputableNoiseDiagram.Contour.RawPaths

set_option autoImplicit false

noncomputable section

namespace FLD.Geometry

open MeasureTheory

/-- The product-site coordinates used by the three-box geometry in UND.Site 4. -/
def toSite (w : ISite) : UND.Site 4 := site w.1 w.2

theorem toSite_injective : Function.Injective toSite := by
  rintro ⟨⟨a, b⟩, P⟩ ⟨⟨a', b'⟩, P'⟩ h
  have ha : a = a' := by simpa [toSite, site] using congrFun h 0
  have hb : b = b' := by simpa [toSite, site] using congrFun h 1
  have hP : P = P' := by
    funext i
    simpa [toSite, site] using congrFun h i.succ.succ
  exact Prod.ext (Prod.ext ha hb) hP

/-- Physical space-time coordinates in the two-sided noise index set. -/
def noiseCoord (y : Pt) : ℤ × UND.Site 4 := (y.2, toSite y.1)

theorem noiseCoord_injective : Function.Injective noiseCoord := by
  intro y y' h
  exact Prod.ext (toSite_injective (congrArg Prod.snd h)) (congrArg Prod.fst h)

/-- Actual replacement flag at a product site and integer time. -/
def flagsOf {A : UND.CA 4} (ω : A.Noise₂) (t : ℤ) (w : ISite) : Prop :=
  (ω (t, toSite w)).1 = true

/-- Distinct physical flags have exactly the product probability, for any CA on Z4. -/
theorem flags_measure (A : UND.CA 4) {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1)
    (Fl : Finset Pt) :
    A.noiseLaw₂ e {ω | ∀ y ∈ Fl, flagsOf ω y.2 y.1} = ENNReal.ofReal e ^ Fl.card := by
  have heq : {ω : A.Noise₂ | ∀ y ∈ Fl, flagsOf ω y.2 y.1} =
      {ω | ∀ p ∈ Fl.image noiseCoord, (ω p).1 = true} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.mem_image]
    constructor
    · rintro h p ⟨y, hy, rfl⟩
      exact h y hy
    · intro h y hy
      exact h _ ⟨y, hy, rfl⟩
  rw [heq, UND.Raw.noiseLaw₂_flags_eq A h0 h1,
    Finset.card_image_of_injective Fl noiseCoord_injective]

end FLD.Geometry
