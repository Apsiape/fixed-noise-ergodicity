/-
# Complete histories: an unmarked live reading gives a tiling (nodes C5–C6)

Paper (Section 2, "Complete histories: the qualitative route"): "Fix all two-sided flags and
values. A complete trajectory is a sequence `(X_t)_{t ∈ ℤ}` satisfying the prescribed local update
at every integer time. For any fixed finite transverse span, the inductions of Lemmas `nw:same`
and `nw:neighbours` use only finitely many past steps. With an unlimited past their conclusions
hold at every span. Thus all unmarked live readings at a planar site and time have one letter,
and neighbouring planar readings match. Let `V_t ⊂ ℤ²` be the planar sites admitting an unmarked
live reading at time `t`. A good provider exists at every such output, and supplies five unmarked
live old inputs. Consequently `V_t + Γ ⊂ V_{t-1}`. … Therefore on a non-tiling input every live
reading of every complete trajectory lies in `𝓜`."

Formalization (deterministic; `D` is a trajectory from every time, i.e. complete):
* `ul_down` (labels persist backwards), `ul_move` (`V_t + Γ ⊂ V_{t-1}`), `ul_reach` (every planar
  site carries an unmarked live reading at some time);
* `ul_same`, `ul_east`, `ul_north`: readings at one planar site carry one tile, readings at
  neighbouring planar sites match (at any two times: both are pushed down to a common time and
  compared by `coh_rel`);
* **`tiles_of_UL`**: one unmarked live reading gives a tiling of the plane, directly (the letters
  read at the planar sites form a tiling; no compactness is needed here, unlike the printed route
  through legal squares of every size, see `STATUS.md`, F1);
* **`live_marked`**: on a non-tiling input every live reading of every complete trajectory is
  marked.
-/
import ForgettingNaturalRule.Coherence.Rel

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace FNR.Coh

open UND.Rule (ISite Prov provOff)
open UND.Coh (MClosed sep)
open FNR.Rule
open FNE (Plane WangSet)

variable {R : WangSet} {D : ℤ → ISite → Option R} {E M : ℤ → ISite → Prop}

/-- Labels persist backwards: an unmarked live reading of `a` at time `t` gives one at every
earlier time, at the same planar site. -/
theorem ul_down (hX : ∀ s, IsTraj s D E) (hM : MClosed E M) {t : ℤ} {u : Plane}
    {P : Fin 4 → ℤ} {a : R} (h : UL D M t (u, P) a) :
    ∀ k : ℕ, ∃ P', UL D M (t - k) (u, P') a := by
  intro k
  induction k with
  | zero => exact ⟨P, by simpa using h⟩
  | succ k ih =>
    obtain ⟨P', hP'⟩ := ih
    obtain ⟨P'', h'', -⟩ := coh_back (hX (t - k - 1)) hM (by omega) hP'
    refine ⟨P'', ?_⟩
    rwa [show t - ((k + 1 : ℕ) : ℤ) = t - k - 1 by push_cast; ring]

/-- `V_t + Γ ⊂ V_{t-1}`, in the form used here. -/
theorem ul_move (hX : ∀ s, IsTraj s D E) (hM : MClosed E M) {u γ : Plane} (hγ : γ ∈ cardinal)
    (h : ∃ t P a, UL D M t (u, P) a) : ∃ t P a, UL D M t (u + γ, P) a := by
  obtain ⟨t, P, a, hu⟩ := h
  obtain ⟨P', -, hn⟩ := coh_back (hX (t - 1)) hM (by omega) hu
  obtain ⟨b, hb⟩ := hn γ hγ
  exact ⟨t - 1, P', b, hb⟩

theorem add_pair (u : Plane) (a b c d : ℤ) : u + (a, b) + (c, d) = u + (a + c, b + d) := by
  ext <;> simp [add_assoc]

/-- Every planar site carries an unmarked live reading at some time. -/
theorem ul_reach (hX : ∀ s, IsTraj s D E) (hM : MClosed E M) {u0 : Plane}
    (h : ∃ t P a, UL D M t (u0, P) a) : ∀ u, ∃ t P a, UL D M t (u, P) a := by
  have h0 : ∃ t P a, UL D M t (u0 + (0, 0), P) a := by rwa [plane_add_zero]
  have hx : ∀ m : ℤ, ∃ t P a, UL D M t (u0 + (m, 0), P) a := by
    intro m
    refine Int.induction_on m h0 (fun i ih => ?_) (fun i ih => ?_)
    · have := ul_move hX hM mem_cardinal_e1 ih
      rwa [add_pair, add_zero] at this
    · have := ul_move hX hM mem_cardinal_w1 ih
      rwa [add_pair, add_zero, ← sub_eq_add_neg] at this
  have hy : ∀ m n : ℤ, ∃ t P a, UL D M t (u0 + (m, n), P) a := by
    intro m n
    refine Int.induction_on n (hx m) (fun i ih => ?_) (fun i ih => ?_)
    · have := ul_move hX hM mem_cardinal_e2 ih
      rwa [add_pair, add_zero] at this
    · have := ul_move hX hM mem_cardinal_w2 ih
      rwa [add_pair, add_zero, ← sub_eq_add_neg] at this
  intro u
  have := hy (u.1 - u0.1) (u.2 - u0.2)
  rwa [show u0 + (u.1 - u0.1, u.2 - u0.2) = u by ext <;> simp] at this

/-- Push two readings down to a common time. -/
theorem ul_common (hX : ∀ s, IsTraj s D E) (hM : MClosed E M) {t t' : ℤ} {u u' : Plane}
    {P P' : Fin 4 → ℤ} {a a' : R} (h : UL D M t (u, P) a) (h' : UL D M t' (u', P') a') :
    ∃ Q Q', UL D M (min t t') (u, Q) a ∧ UL D M (min t t') (u', Q') a' := by
  obtain ⟨Q, hQ⟩ := ul_down hX hM h (t - min t t').toNat
  obtain ⟨Q', hQ'⟩ := ul_down hX hM h' (t' - min t t').toNat
  rw [show t - ((t - min t t').toNat : ℤ) = min t t' by omega] at hQ
  rw [show t' - ((t' - min t t').toNat : ℤ) = min t t' by omega] at hQ'
  exact ⟨Q, Q', hQ, hQ'⟩

/-- **Same planar site** (Lemma `nw:same` with an unlimited past): one tile. -/
theorem ul_same (hX : ∀ s, IsTraj s D E) (hM : MClosed E M) {t t' : ℤ} {u : Plane}
    {P P' : Fin 4 → ℤ} {a a' : R} (h : UL D M t (u, P) a) (h' : UL D M t' (u, P') a') :
    a = a' := by
  obtain ⟨Q, Q', hQ, hQ'⟩ := ul_common hX hM h h'
  refine (coh_rel (hX (min t t' - sep Q Q' - 1)) hM (sep Q Q') (min t t') u Q Q' (0, 0) a a'
    (by decide) rfl (by omega) hQ (by rwa [plane_add_zero])).1 rfl

/-- **East neighbours** (Lemma `nw:neighbours` with an unlimited past). -/
theorem ul_east (hX : ∀ s, IsTraj s D E) (hM : MClosed E M) {t t' : ℤ} {u : Plane}
    {P P' : Fin 4 → ℤ} {a a' : R} (h : UL D M t (u, P) a) (h' : UL D M t' (u + (1, 0), P') a') :
    a.1.E = a'.1.W := by
  obtain ⟨Q, Q', hQ, hQ'⟩ := ul_common hX hM h h'
  exact (coh_rel (hX (min t t' - sep Q Q' - 1)) hM (sep Q Q') (min t t') u Q Q' (1, 0) a a'
    (by decide) rfl (by omega) hQ hQ').2.1 rfl

/-- **North neighbours** (Lemma `nw:neighbours` with an unlimited past). -/
theorem ul_north (hX : ∀ s, IsTraj s D E) (hM : MClosed E M) {t t' : ℤ} {u : Plane}
    {P P' : Fin 4 → ℤ} {a a' : R} (h : UL D M t (u, P) a) (h' : UL D M t' (u + (0, 1), P') a') :
    a.1.N = a'.1.S := by
  obtain ⟨Q, Q', hQ, hQ'⟩ := ul_common hX hM h h'
  exact (coh_rel (hX (min t t' - sep Q Q' - 1)) hM (sep Q Q') (min t t') u Q Q' (0, 1) a a'
    (by decide) rfl (by omega) hQ hQ').2.2 rfl

/-- **One unmarked live reading in a complete trajectory gives a tiling of the plane.** -/
theorem tiles_of_UL (hX : ∀ s, IsTraj s D E) (hM : MClosed E M)
    (h : ∃ t w a, UL D M t w a) : TilesPlane R := by
  obtain ⟨t0, ⟨u0, P0⟩, a0, h0⟩ := h
  have hr := ul_reach hX hM ⟨t0, P0, a0, h0⟩
  choose T Pf A hA using hr
  exact ⟨fun u => (A u).1, fun u => (A u).2, fun u => ul_east hX hM (hA u) (hA (u + (1, 0))),
    fun u => ul_north hX hM (hA u) (hA (u + (0, 1)))⟩

/-- **On a non-tiling input every live reading of every complete trajectory is marked.** -/
theorem live_marked (hX : ∀ s, IsTraj s D E) (hM : MClosed E M) (hR : ¬ TilesPlane R)
    {t : ℤ} {w : ISite} (hl : D t w ≠ none) : M t w := by
  by_contra hm
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hl
  exact hR (tiles_of_UL hX hM ⟨t, w, a, hm, ha⟩)

end FNR.Coh
