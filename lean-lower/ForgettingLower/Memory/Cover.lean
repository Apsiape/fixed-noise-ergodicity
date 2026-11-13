/- Finite-past clone and blank error covers for the actual three-box rule. -/
import ForgettingLower.Rule.Bridge

set_option autoImplicit false

noncomputable section

namespace FLD.Memory

open FLD.Geometry FLD.Rule
open FNE (Plane WangSet box)

variable {R : WangSet} {D : ℤ → ISite → Option R} {E : ℤ → ISite → Prop}

theorem traj_succ (hX : IsTraj 0 D E) {n : ℕ} {w : ISite} (hE : ¬ E ((n + 1 : ℕ) : ℤ) w) :
    D ((n + 1 : ℕ) : ℤ) w = GI (D n) w := by
  have := hX ((n + 1 : ℕ) : ℤ) w (by omega) hE
  rwa [show ((n + 1 : ℕ) : ℤ) - 1 = n by push_cast; ring] at this

/-- **The clone reference** (Lemma `nw:memorycover`, first inclusion): from the clone of a legal
pattern, every error at time `n` is in the marked field begun empty at time `0`. -/
theorem clone_cover {θ : Plane → R} (hθ : Legal θ) (hX : IsTraj 0 D E) (h0 : D 0 = clone θ) :
    ∀ n : ℕ, ∀ w, D n w ≠ clone θ w → markedFrom E 0 n w := by
  classical
  intro n
  induction n with
  | zero =>
    intro w hw
    apply hw
    have := congrFun h0 w
    simpa using this
  | succ n ih =>
    intro w hw
    show E (0 + ((n + 1 : ℕ) : ℤ)) w ∨ TwoCl (markedFrom E 0 n) w
    by_cases hE : E ((n + 1 : ℕ) : ℤ) w
    · exact Or.inl (by rwa [zero_add])
    · refine Or.inr (twoCl_of_card ?_)
      rw [traj_succ hX hE] at hw
      refine lt_of_lt_of_le (card_bad_of_ne_clone hθ hw) (Finset.card_le_card fun π hπ => ?_)
      rw [Finset.mem_filter] at hπ ⊢
      obtain ⟨γ, hγ, hne⟩ := hπ.2
      exact ⟨Finset.mem_univ _, γ, cardinal_sub_box γ hγ, ih _ hne⟩

/-- **The blank reference** (Lemma `nw:memorycover`, second inclusion): from the all-blank
configuration, every live letter at time `n` is in the marked field begun empty at time `0`. -/
theorem blank_cover (hX : IsTraj 0 D E) (h0 : D 0 = fun _ => none) :
    ∀ n : ℕ, ∀ w, D n w ≠ none → markedFrom E 0 n w := by
  classical
  intro n
  induction n with
  | zero =>
    intro w hw
    apply hw
    have := congrFun h0 w
    simpa using this
  | succ n ih =>
    intro w hw
    show E (0 + ((n + 1 : ℕ) : ℤ)) w ∨ TwoCl (markedFrom E 0 n) w
    by_cases hE : E ((n + 1 : ℕ) : ℤ) w
    · exact Or.inl (by rwa [zero_add])
    · refine Or.inr (twoCl_of_card ?_)
      rw [traj_succ hX hE] at hw
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hw
      have hK : K < quorum := by norm_num [K, quorum]
      refine lt_of_lt_of_le hK ((GI_live_centres hs).trans (Finset.card_le_card fun π hπ => ?_))
      rw [Finset.mem_filter] at hπ ⊢
      exact ⟨Finset.mem_univ _, 0, by simp [box], by simpa using ih _ hπ.2⟩

/-- The marked field begun empty at time `0` lies in `𝓜`. -/
theorem marked_of_markedFrom {n : ℕ} {w : ISite} (h : markedFrom E 0 n w) : marked E n w :=
  ⟨n, by rwa [sub_self]⟩

end FLD.Memory
