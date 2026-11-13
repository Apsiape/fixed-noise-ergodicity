/- Planar edge matching is proved separately from same-site agreement.
A clean checker star is compared at its neighbouring site one time earlier. -/
import ForgettingLower.Coherence.Same

set_option autoImplicit false

noncomputable section
namespace FLD.Coh
open FLD.Geometry FLD.Rule
open FNE (Plane WangSet)
open MeasureTheory

variable {R : WangSet} {X : ℤ → ISite → Option R} {E : ℤ → ISite → Prop}

/-- East-facing edges match, with arbitrary transverse positions. -/
theorem east_edge (hX : IsHistory X E) (hden : DensityEvent E)
    {t : ℤ} {u : Plane} {P Q : Fin 2 → ℤ} {a b : R}
    (h : UL X (marked E) t (u, P) a)
    (h' : UL X (marked E) t (u + (1, 0), Q) b) : a.1.E = b.1.W := by
  obtain ⟨π, hc, hm⟩ := exists_good hX h
  obtain ⟨c, he, hmatch⟩ := (chkI_eq_some.mp hc).2.1
  have hcUL : UL X (marked E) (t - 1) (u + (1, 0), P + offset π) c :=
    ⟨fun hm' => hm ⟨(1, 0), cardinal_sub_box _ mem_cardinal_e1, hm'⟩, he⟩
  obtain ⟨π', hc', hm'⟩ := exists_good hX h'
  have hbUL := ul_of_good hc' hm'
  rw [same_site hX hden hcUL hbUL] at hmatch
  exact hmatch

/-- North-facing edges match, with arbitrary transverse positions. -/
theorem north_edge (hX : IsHistory X E) (hden : DensityEvent E)
    {t : ℤ} {u : Plane} {P Q : Fin 2 → ℤ} {a b : R}
    (h : UL X (marked E) t (u, P) a)
    (h' : UL X (marked E) t (u + (0, 1), Q) b) : a.1.N = b.1.S := by
  obtain ⟨π, hc, hm⟩ := exists_good hX h
  obtain ⟨c, he, hmatch⟩ := (chkI_eq_some.mp hc).2.2.2.1
  have hcUL : UL X (marked E) (t - 1) (u + (0, 1), P + offset π) c :=
    ⟨fun hm' => hm ⟨(0, 1), cardinal_sub_box _ mem_cardinal_e2, hm'⟩, he⟩
  obtain ⟨π', hc', hm'⟩ := exists_good hX h'
  have hbUL := ul_of_good hc' hm'
  rw [same_site hX hden hcUL hbUL] at hmatch
  exact hmatch

/-- West-facing matching follows by reading the east edge at the western site. -/
theorem west_edge (hX : IsHistory X E) (hden : DensityEvent E)
    {t : ℤ} {u : Plane} {P Q : Fin 2 → ℤ} {a b : R}
    (h : UL X (marked E) t (u, P) a)
    (h' : UL X (marked E) t (u + (-1, 0), Q) b) : b.1.E = a.1.W := by
  have he : u + (-1, 0) + (1, 0) = u := by ext <;> simp
  exact east_edge hX hden h' (by rwa [he])

/-- South-facing matching follows by reading the north edge at the southern site. -/
theorem south_edge (hX : IsHistory X E) (hden : DensityEvent E)
    {t : ℤ} {u : Plane} {P Q : Fin 2 → ℤ} {a b : R}
    (h : UL X (marked E) t (u, P) a)
    (h' : UL X (marked E) t (u + (0, -1), Q) b) : b.1.N = a.1.S := by
  have he : u + (0, -1) + (0, 1) = u := by ext <;> simp
  exact north_edge hX hden h' (by rwa [he])

/-- Lemma ld:z4edges holds for every complete history on the common flag event. -/
theorem edge_matching_ae (R : WangSet) {e : ℝ} (h0 : 0 ≤ e) (he : e ≤ eps0) :
    ∀ᵐ ω ∂((natCA R).noiseLaw₂ e), ∀ X : ℤ → (natCA R).Config,
      (natCA R).IsComplete ω X → ∀ (t : ℤ) (u : Plane) (P Q : Fin 2 → ℤ) (a b : R),
        UL (fun s => dec (X s)) (marked (flagsOf ω)) t (u, P) a →
        (UL (fun s => dec (X s)) (marked (flagsOf ω)) t (u + (1, 0), Q) b → a.1.E = b.1.W) ∧
        (UL (fun s => dec (X s)) (marked (flagsOf ω)) t (u + (0, 1), Q) b → a.1.N = b.1.S) := by
  filter_upwards [Density.all_path_density (natCA R) h0 he] with ω hω
  intro X hX t u P Q a b h
  exact ⟨fun h' => east_edge (isHistory_of_complete hX) hω h h',
    fun h' => north_edge (isHistory_of_complete hX) hω h h'⟩

end FLD.Coh
