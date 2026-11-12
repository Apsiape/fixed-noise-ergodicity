/-
# The forgetting branch: non-tiling implies ergodicity (nodes P2, P3)

Paper (Section 2, "Complete histories: the qualitative route"): "If two complete trajectories with
the same innovations differ at a vertex, that vertex is unflagged, is live in at least one
trajectory, and hence is marked. It has a discrepant actual parent. Iteration would give an
infinite ordinary marked path, excluded almost surely by Lemma `nw:paths`. This exclusion is
simultaneous at every root and the deterministic implication is simultaneous for every complete
trajectory. Thus there is almost surely at most one complete history. … This qualitative route
proves all-law ergodicity by Lemma `nw:ergodic`."

* `disc_step`, `disc_path` (deterministic): a discrepancy between two complete trajectories of
  `natCA R` with the same noise, on a non-tiling input, is marked and propagates to a discrepant
  actual parent along an ordinary step, so it starts an infinite marked backward path;
* **`unique_complete`**: almost surely all complete trajectories agree at time `0`;
* **`ergodic_of_not_tiles`**: with the noise-diagram core's Lemma 8.5 (`UND.CA.ergodic_of_unique`,
  REUSE: a.s. unique complete trajectories imply ergodicity), `G_R` is ergodic at every
  `0 ≤ ε ≤ ε_*` when `R` does not tile.
-/
import ForgettingNaturalRule.Forget.Paths
import ForgettingNaturalRule.Coherence.Tiling
import ForgettingNaturalRule.Rule.Bridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace FNR.Forget

open UND.Raw (OrdStep)
open UND.Coh (marked flagsOf marked_closed)
open UND.Rule (ISite provOff)
open FNR.Rule
open FNE (WangSet)

variable {R : WangSet}

/-- **One discrepancy step.** On a non-tiling input, a discrepancy between two complete
trajectories with the same noise is marked and has a discrepant actual parent one step earlier. -/
theorem disc_step (hR : ¬ TilesPlane R) {ω : (natCA R).Noise₂} {X Y : ℤ → (natCA R).Config}
    (hX : (natCA R).IsComplete ω X) (hY : (natCA R).IsComplete ω Y) {t : ℤ} {w : ISite}
    (h : dec (X t) w ≠ dec (Y t) w) :
    marked (flagsOf ω) t w ∧ ∃ w', OrdStep w w' ∧ dec (X (t - 1)) w' ≠ dec (Y (t - 1)) w' := by
  have hE : ¬ flagsOf ω t w := fun hE => h (complete_flag_eq hX hY hE)
  refine ⟨?_, ?_⟩
  · by_cases hl : dec (X t) w = none
    · have hl' : dec (Y t) w ≠ none := fun h' => h (hl.trans h'.symm)
      exact FNR.Coh.live_marked (isTraj_of_complete hY) (marked_closed _) hR hl'
    · exact FNR.Coh.live_marked (isTraj_of_complete hX) (marked_closed _) hR hl
  · have e1 : dec (X t) w = GI (dec (X (t - 1))) w :=
      isTraj_of_complete hX (t - 1) t w (by omega) hE
    have e2 : dec (Y t) w = GI (dec (Y (t - 1))) w :=
      isTraj_of_complete hY (t - 1) t w (by omega) hE
    rw [e1, e2] at h
    obtain ⟨γ, hγ, π, hne⟩ := disc_parent h
    exact ⟨(w.1 + γ, w.2 + provOff π), ⟨γ, cardinal_sub_box γ hγ, π, rfl⟩, hne⟩

/-- **A discrepancy starts an infinite marked backward ordinary path.** -/
theorem disc_path (hR : ¬ TilesPlane R) {ω : (natCA R).Noise₂} {X Y : ℤ → (natCA R).Config}
    (hX : (natCA R).IsComplete ω X) (hY : (natCA R).IsComplete ω Y) {t : ℤ} {w : ISite}
    (h : dec (X t) w ≠ dec (Y t) w) :
    ∃ p : ℕ → ISite, p 0 = w ∧ (∀ k, OrdStep (p k) (p (k + 1))) ∧
      ∀ k : ℕ, marked (flagsOf ω) (t - k) (p k) := by
  classical
  let Disc : ℕ → ISite → Prop := fun k v => dec (X (t - k)) v ≠ dec (Y (t - k)) v
  have hstep : ∀ k v, Disc k v →
      marked (flagsOf ω) (t - k) v ∧ ∃ v', OrdStep v v' ∧ Disc (k + 1) v' := by
    intro k v hv
    obtain ⟨hm, v', hs, hd⟩ := disc_step hR hX hY hv
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

/-- **Almost surely there is at most one complete history** (non-tiling input,
`0 ≤ ε ≤ ε_*`). -/
theorem unique_complete (hR : ¬ TilesPlane R) {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ epsStar) :
    ∀ᵐ ω ∂((natCA R).noiseLaw₂ ε), ∀ X Y : ℤ → (natCA R).Config,
      (natCA R).IsComplete ω X → (natCA R).IsComplete ω Y → X 0 = Y 0 := by
  filter_upwards [raw_paths_nat (natCA R) h0 hε] with ω hω X Y hX hY
  apply dec_inj
  funext w
  by_contra hne
  obtain ⟨p, -, hs, hm⟩ := disc_path hR hX hY hne
  exact hω 0 p hs hm

/-- **The forgetting branch of Theorem D**: if `R` does not tile the plane, `G_R` is ergodic at
every `0 ≤ ε ≤ ε_*`. -/
theorem ergodic_of_not_tiles (hR : ¬ TilesPlane R) {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ epsStar) :
    (natCA R).IsErgodic ε :=
  ((natCA R).ergodic_of_unique h0 (hε.trans Const.epsStar_le_one)
    (unique_complete hR h0 hε)).1

end FNR.Forget
