/- Planar extraction from complete histories, using separate coherence and edge proofs. -/
import ForgettingLower.Coherence.Edges

set_option autoImplicit false

noncomputable section

namespace FLD.Coh

open FLD.Geometry FLD.Rule
open FNE (Plane WangSet)
open MeasureTheory

variable {R : WangSet} {D : ℤ → ISite → Option R} {E : ℤ → ISite → Prop}

/-- Labels persist backwards: an unmarked live reading of `a` at time `t` gives one at every
earlier time, at the same planar site. -/
theorem ul_down (hX : IsHistory D E) {t : ℤ} {u : Plane}
    {P : Fin 2 → ℤ} {a : R} (h : UL D (marked E) t (u, P) a) :
    ∀ k : ℕ, ∃ P', UL D (marked E) (t - k) (u, P') a := by
  intro k
  induction k with
  | zero => exact ⟨P, by simpa using h⟩
  | succ k ih =>
    obtain ⟨P', hP'⟩ := ih
    obtain ⟨P'', h'', -⟩ := coh_back hX hP'
    refine ⟨P'', ?_⟩
    rwa [show t - ((k + 1 : ℕ) : ℤ) = t - k - 1 by push_cast; ring]

/-- `V_t + Γ ⊂ V_{t-1}`, in the form used here. -/
theorem ul_move (hX : IsHistory D E) {u γ : Plane} (hγ : γ ∈ cardinal)
    (h : ∃ t P a, UL D (marked E) t (u, P) a) : ∃ t P a, UL D (marked E) t (u + γ, P) a := by
  obtain ⟨t, P, a, hu⟩ := h
  obtain ⟨P', -, hn⟩ := coh_back hX hu
  obtain ⟨b, hb⟩ := hn γ hγ
  exact ⟨t - 1, P', b, hb⟩

theorem add_pair (u : Plane) (a b c d : ℤ) : u + (a, b) + (c, d) = u + (a + c, b + d) := by
  ext <;> simp [add_assoc]

/-- Every planar site carries an unmarked live reading at some time. -/
theorem ul_reach (hX : IsHistory D E) {u0 : Plane}
    (h : ∃ t P a, UL D (marked E) t (u0, P) a) : ∀ u, ∃ t P a, UL D (marked E) t (u, P) a := by
  have h0 : ∃ t P a, UL D (marked E) t (u0 + (0, 0), P) a := by rwa [plane_add_zero]
  have hx : ∀ m : ℤ, ∃ t P a, UL D (marked E) t (u0 + (m, 0), P) a := by
    intro m
    refine Int.induction_on m h0 (fun i ih => ?_) (fun i ih => ?_)
    · have := ul_move hX mem_cardinal_e1 ih
      rwa [add_pair, add_zero] at this
    · have := ul_move hX mem_cardinal_w1 ih
      rwa [add_pair, add_zero, ← sub_eq_add_neg] at this
  have hy : ∀ m n : ℤ, ∃ t P a, UL D (marked E) t (u0 + (m, n), P) a := by
    intro m n
    refine Int.induction_on n (hx m) (fun i ih => ?_) (fun i ih => ?_)
    · have := ul_move hX mem_cardinal_e2 ih
      rwa [add_pair, add_zero] at this
    · have := ul_move hX mem_cardinal_w2 ih
      rwa [add_pair, add_zero, ← sub_eq_add_neg] at this
  intro u
  have := hy (u.1 - u0.1) (u.2 - u0.2)
  rwa [show u0 + (u.1 - u0.1, u.2 - u0.2) = u by ext <;> simp] at this

/-- Push two readings down to a common time. -/
theorem ul_common (hX : IsHistory D E) {t t' : ℤ} {u u' : Plane}
    {P P' : Fin 2 → ℤ} {a a' : R} (h : UL D (marked E) t (u, P) a) (h' : UL D (marked E) t' (u', P') a') :
    ∃ Q Q', UL D (marked E) (min t t') (u, Q) a ∧ UL D (marked E) (min t t') (u', Q') a' := by
  obtain ⟨Q, hQ⟩ := ul_down hX h (t - min t t').toNat
  obtain ⟨Q', hQ'⟩ := ul_down hX h' (t' - min t t').toNat
  rw [show t - ((t - min t t').toNat : ℤ) = min t t' by omega] at hQ
  rw [show t' - ((t' - min t t').toNat : ℤ) = min t t' by omega] at hQ'
  exact ⟨Q, Q', hQ, hQ'⟩

/-- Readings at one planar site agree even at different times. -/
theorem ul_same (hX : IsHistory D E) (hden : DensityEvent E) {t t' : ℤ} {u : Plane}
    {P P' : Fin 2 → ℤ} {a a' : R} (h : UL D (marked E) t (u, P) a)
    (h' : UL D (marked E) t' (u, P') a') : a = a' := by
  obtain ⟨Q, Q', hQ, hQ'⟩ := ul_common hX h h'
  exact same_site hX hden hQ hQ'

/-- East neighbours match after preserving both labels to a common time. -/
theorem ul_east (hX : IsHistory D E) (hden : DensityEvent E) {t t' : ℤ} {u : Plane}
    {P P' : Fin 2 → ℤ} {a a' : R} (h : UL D (marked E) t (u, P) a)
    (h' : UL D (marked E) t' (u + (1, 0), P') a') : a.1.E = a'.1.W := by
  obtain ⟨Q, Q', hQ, hQ'⟩ := ul_common hX h h'
  exact east_edge hX hden hQ hQ'

/-- North neighbours match after preserving both labels to a common time. -/
theorem ul_north (hX : IsHistory D E) (hden : DensityEvent E) {t t' : ℤ} {u : Plane}
    {P P' : Fin 2 → ℤ} {a a' : R} (h : UL D (marked E) t (u, P) a)
    (h' : UL D (marked E) t' (u + (0, 1), P') a') : a.1.N = a'.1.S := by
  obtain ⟨Q, Q', hQ, hQ'⟩ := ul_common hX h h'
  exact north_edge hX hden hQ hQ'

/-- **One unmarked live reading in a complete trajectory gives a tiling of the plane.** -/
theorem tiles_of_UL (hX : IsHistory D E) (hden : DensityEvent E)
    (h : ∃ t w a, UL D (marked E) t w a) : TilesPlane R := by
  obtain ⟨t0, ⟨u0, P0⟩, a0, h0⟩ := h
  have hr := ul_reach hX ⟨t0, P0, a0, h0⟩
  choose T Pf A hA using hr
  exact ⟨fun u => (A u).1, fun u => (A u).2, fun u => ul_east hX hden (hA u) (hA (u + (1, 0))),
    fun u => ul_north hX hden (hA u) (hA (u + (0, 1)))⟩

/-- **On a non-tiling input every live reading of every complete trajectory is marked.** -/
theorem live_marked (hX : IsHistory D E) (hden : DensityEvent E) (hR : ¬ TilesPlane R)
    {t : ℤ} {w : ISite} (hl : D t w ≠ none) : marked E t w := by
  by_contra hm
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hl
  exact hR (tiles_of_UL hX hden ⟨t, w, a, hm, ha⟩)

/-- Extraction holds for every genuine complete history on the common noise event. -/
theorem extraction_ae (R : WangSet) {e : ℝ} (h0 : 0 ≤ e) (he : e ≤ eps0) :
    ∀ᵐ ω ∂((natCA R).noiseLaw₂ e), ∀ X : ℤ → (natCA R).Config,
      (natCA R).IsComplete ω X →
        (∃ t w a, UL (fun s => dec (X s)) (marked (flagsOf ω)) t w a) → TilesPlane R := by
  filter_upwards [Density.all_path_density (natCA R) h0 he] with ω hω
  intro X hX h
  exact tiles_of_UL (isHistory_of_complete hX) hω h

end FLD.Coh
