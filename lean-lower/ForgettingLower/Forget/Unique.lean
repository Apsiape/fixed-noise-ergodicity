/- Complete-history uniqueness from planar extraction and the density event. -/
import ForgettingLower.Coherence.Tiling
import UncomputableNoiseDiagram.PCA.Attraction

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace FLD.Forget

open FLD.Geometry FLD.Rule
open FLD.Coh (isHistory_of_complete)
open FNE (WangSet)

variable {R : WangSet}

/-- **One discrepancy step.** On a non-tiling input, a discrepancy between two complete
trajectories with the same noise is marked and has a discrepant actual parent one step earlier. -/
theorem disc_step (hR : ¬ TilesPlane R) {ω : (natCA R).Noise₂} {X Y : ℤ → (natCA R).Config}
    (hX : (natCA R).IsComplete ω X) (hY : (natCA R).IsComplete ω Y)
    (hden : Coh.DensityEvent (flagsOf ω)) {t : ℤ} {w : ISite}
    (h : dec (X t) w ≠ dec (Y t) w) :
    marked (flagsOf ω) t w ∧ ∃ w', OrdStep w w' ∧ dec (X (t - 1)) w' ≠ dec (Y (t - 1)) w' := by
  have hE : ¬ flagsOf ω t w := fun hE => h (complete_flag_eq hX hY hE)
  refine ⟨?_, ?_⟩
  · by_cases hl : dec (X t) w = none
    · have hl' : dec (Y t) w ≠ none := fun h' => h (hl.trans h'.symm)
      exact Coh.live_marked (isHistory_of_complete hY) hden hR hl'
    · exact Coh.live_marked (isHistory_of_complete hX) hden hR hl
  · have e1 : dec (X t) w = GI (dec (X (t - 1))) w :=
      isTraj_of_complete hX (t - 1) t w (by omega) hE
    have e2 : dec (Y t) w = GI (dec (Y (t - 1))) w :=
      isTraj_of_complete hY (t - 1) t w (by omega) hE
    rw [e1, e2] at h
    obtain ⟨γ, hγ, π, hne⟩ := disc_parent h
    exact ⟨(w.1 + γ, w.2 + offset π), ⟨γ, cardinal_sub_box γ hγ, π, rfl⟩, hne⟩

/-- **A discrepancy starts an infinite marked backward ordinary path.** -/
theorem disc_path (hR : ¬ TilesPlane R) {ω : (natCA R).Noise₂} {X Y : ℤ → (natCA R).Config}
    (hX : (natCA R).IsComplete ω X) (hY : (natCA R).IsComplete ω Y)
    (hden : Coh.DensityEvent (flagsOf ω)) {t : ℤ} {w : ISite}
    (h : dec (X t) w ≠ dec (Y t) w) :
    ∃ p : ℕ → ISite, p 0 = w ∧ (∀ k, OrdStep (p k) (p (k + 1))) ∧
      ∀ k : ℕ, marked (flagsOf ω) (t - k) (p k) := by
  classical
  let Disc : ℕ → ISite → Prop := fun k v => dec (X (t - k)) v ≠ dec (Y (t - k)) v
  have hstep : ∀ k v, Disc k v →
      marked (flagsOf ω) (t - k) v ∧ ∃ v', OrdStep v v' ∧ Disc (k + 1) v' := by
    intro k v hv
    obtain ⟨hm, v', hs, hd⟩ := disc_step hR hX hY hden hv
    refine ⟨hm, v', hs, ?_⟩
    show dec (X (t - ((k + 1 : ℕ) : ℤ))) v' ≠ dec (Y (t - ((k + 1 : ℕ) : ℤ))) v'
    rwa [show t - ((k + 1 : ℕ) : ℤ) = t - k - 1 by push_cast; ring]
  choose! nxt hnxt using fun k v (hv : Disc k v) => (hstep k v hv).2
  let p : ℕ → ISite := fun k => Nat.rec w (fun k pk => nxt k pk) k
  have hp : ∀ k, Disc k (p k) := by
    intro k
    induction k with
    | zero =>
      show dec (X (t - ((0 : ℕ) : ℤ))) w ≠ dec (Y (t - ((0 : ℕ) : ℤ))) w
      simpa using h
    | succ k ih => exact (hnxt k (p k) ih).2
  exact ⟨p, rfl, fun k => (hnxt k (p k) (hp k)).1, fun k => (hstep k (p k) (hp k)).1⟩

/-- Complete histories agree at every integer time on one probability-one event. -/
theorem unique_complete_all (hR : ¬ TilesPlane R) {e : ℝ} (h0 : 0 ≤ e) (he : e ≤ eps0) :
    ∀ᵐ ω ∂((natCA R).noiseLaw₂ e), ∀ X Y : ℤ → (natCA R).Config,
      (natCA R).IsComplete ω X → (natCA R).IsComplete ω Y → ∀ t, X t = Y t := by
  filter_upwards [Density.all_path_density (natCA R) h0 he,
    Density.raw_paths (natCA R) h0 he] with ω hden hpaths
  intro X Y hX hY t
  apply dec_inj
  funext w
  by_contra hne
  obtain ⟨p, -, hs, hm⟩ := disc_path hR hX hY hden hne
  exact hpaths t p hs hm

/-- The time-zero form required by the generic attraction theorem. -/
theorem unique_complete (hR : ¬ TilesPlane R) {e : ℝ} (h0 : 0 ≤ e) (he : e ≤ eps0) :
    ∀ᵐ ω ∂((natCA R).noiseLaw₂ e), ∀ X Y : ℤ → (natCA R).Config,
      (natCA R).IsComplete ω X → (natCA R).IsComplete ω Y → X 0 = Y 0 := by
  filter_upwards [unique_complete_all hR h0 he] with ω hω
  exact fun X Y hX hY => hω X Y hX hY 0

/-- Non-tiling implies a unique invariant probability law attracting every initial law. -/
theorem ergodic_of_not_tiles (hR : ¬ TilesPlane R) {e : ℝ} (h0 : 0 ≤ e) (he : e ≤ eps0) :
    (natCA R).IsErgodic e :=
  ((natCA R).ergodic_of_unique h0 (he.trans Const.eps0_le_one)
    (unique_complete hR h0 he)).1

end FLD.Forget
