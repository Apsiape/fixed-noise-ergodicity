/-
# The two-cluster memory cover (Lemma `nw:memorycover`) (node M2)

Paper (Lemma `nw:memorycover`): "Start one trajectory `X` from `ξ_θ` and another `Y` from all blank.
For every time, every site and every realization, the errors `X_t(u,P) ≠ θ(u)` and the live
readings `Y_t(u,P) ≠ ⊥` are contained in the marked field begun empty at time zero, hence in `𝓜`.
… If at most `K` checked providers were different from `θ(u)`, the other `q - K = h` would force
the correct output. Therefore at least `K + 1` providers are wrong. A checked provider can be
wrong only if at least one of its five cardinal inputs differs from the corresponding cloned tile
… Those `K + 1` provider offsets cannot all lie in one `K`-element cluster. … An unflagged live `Y`
output requires at least `h = 4K` live checked providers. Their old central letters are live.
Since `h > K`, at least two clusters contain such live old centres."

Formalization (deterministic, for any trajectory `D` of `G_R` from time `0` with flags `E`): the
marked field begun empty at time `0` is the noise-diagram core's `UND.Coh.markedFrom E 0`
(REUSE); `marked_of_markedFrom` places it inside `𝓜`.
* `traj_succ`; **`clone_cover`**; **`blank_cover`**; `marked_of_markedFrom`.
-/
import ForgettingNaturalRule.Rule.Local

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace FNR.Memory

open UND.Rule (ISite Prov provOff)
open UND.Coh (markedFrom marked MarkedAt TwoCl)
open FNR.Rule
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
      have hK : UND.Param.K < UND.Param.h := by norm_num [UND.Param.K, UND.Param.h]
      refine lt_of_lt_of_le hK ((GI_live_centres hs).trans (Finset.card_le_card fun π hπ => ?_))
      rw [Finset.mem_filter] at hπ ⊢
      exact ⟨Finset.mem_univ _, 0, by simp [box], by simpa using ih _ hπ.2⟩

/-- The marked field begun empty at time `0` lies in `𝓜`. -/
theorem marked_of_markedFrom {n : ℕ} {w : ISite} (h : markedFrom E 0 n w) : marked E n w :=
  ⟨n, by rwa [sub_self]⟩

end FNR.Memory
