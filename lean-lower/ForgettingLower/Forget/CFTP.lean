/- All integer observation times and finite windows on the same full-measure event. -/
import ForgettingLower.Forget.Unique

set_option autoImplicit false

noncomputable section
namespace FLD.Forget
open MeasureTheory

variable {d : ℕ} (A : UND.CA d)

/-- Translate the time coordinate of a two-sided innovation field. -/
def timeNoise (ω : A.Noise₂) (t : ℤ) : A.Noise₂ := fun p => ω (p.1 + t, p.2)

theorem flow_timeNoise (ω : A.Noise₂) (t s : ℤ) (n : ℕ) (x : A.Config) :
    A.flow (timeNoise A ω t) s n x = A.flow ω (s + t) n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change A.update (fun w => ω (s + (n : ℤ) + 1 + t, w))
      (A.flow (timeNoise A ω t) s n x) =
        A.update (fun w => ω (s + t + (n : ℤ) + 1, w)) (A.flow ω (s + t) n x)
    rw [ih, show s + (n : ℤ) + 1 + t = s + t + (n : ℤ) + 1 by ring]

theorem complete_timeNoise {ω : A.Noise₂} {t : ℤ} {X : ℤ → A.Config}
    (hX : A.IsComplete (timeNoise A ω t) X) :
    A.IsComplete ω (fun s => X (s - t)) := by
  intro s
  have h := hX (s - t)
  change X (s - t + 1) = A.update (fun w => ω (s - t + 1 + t, w)) (X (s - t)) at h
  rw [show s - t + 1 + t = s + 1 by ring] at h
  change X (s + 1 - t) = _
  rw [show s + 1 - t = s - t + 1 by ring]
  exact h

/-- Deterministic compactness repackaging of uniqueness at every time. -/
theorem all_time_singleton {ω : A.Noise₂}
    (huniq : ∀ X Y : ℤ → A.Config, A.IsComplete ω X → A.IsComplete ω Y →
      ∀ t, X t = Y t) (t : ℤ) (O : Finset (UND.Site d)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x y : A.Config, ∀ w ∈ O,
      A.flow ω (t - (n : ℤ)) n x w = A.flow ω (t - (n : ℤ)) n y w := by
  have hu : ∀ X Y : ℤ → A.Config, A.IsComplete (timeNoise A ω t) X →
      A.IsComplete (timeNoise A ω t) Y → ∀ w ∈ O, X 0 w = Y 0 w := by
    intro X Y hX hY w _
    have h := congrFun (huniq _ _ (complete_timeNoise A hX) (complete_timeNoise A hY) t) w
    simpa using h
  obtain ⟨n₀, hn₀⟩ := A.pullback_eventually_singleton_of_unique (timeNoise A ω t) O hu
  refine ⟨n₀, fun n hn x y w hw => ?_⟩
  have h := hn₀ n hn x y w hw
  simpa only [UND.CA.pullback, flow_timeNoise,
    show -(n : ℤ) + t = t - (n : ℤ) by ring] using h

/-- Non-tiling gives the exact frozen all-time, all-start finite-window CFTP statement. -/
theorem allTimeCFTP_of_not_tiles {R : FNE.WangSet} (hR : ¬ TilesPlane R)
    {e : ℝ} (h0 : 0 ≤ e) (he : e ≤ eps0) : AllTimeCFTP (natCA R) e := by
  filter_upwards [unique_complete_all hR h0 he] with ω hω
  exact all_time_singleton (natCA R) hω

end FLD.Forget
