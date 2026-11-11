/-
# Section 2.2: the noisy quorum rule is a positive-rate PCA

The four clauses of `IsPositiveRatePCA` (decision D6):
(i) the rule commutes with every translation of `ℤ² × ℤᵏ` (`quorumRule_translate`, proved here);
(ii) locality on `𝒩 = Λ × {c_0, …, c_k}` (`quorumRule_local`, `Process.lean`);
(iii) the one-step product form (`law_dirac_one`, `Markov.lean`);
(iv) positive rates (`siteLaw_pos`, `Markov.lean`).
-/
import FixedNoiseErgodicity.Section2.Markov

set_option autoImplicit false

noncomputable section

namespace FNE

variable {k : ℕ} {R : WangSet}

/-- The planar checker commutes with planar translations. -/
theorem checker_translate (y : Plane → Sym R) (a u : Plane) :
    checker (fun u' => y (u' + a)) u = checker y (u + a) := by
  have e : ∀ d : Plane, u + d + a = u + a + d := fun d => add_right_comm u d a
  have hk : CheckerKeeps (fun u' => y (u' + a)) u ↔ CheckerKeeps y (u + a) := by
    unfold CheckerKeeps
    constructor
    · rintro ⟨s, hs, hall⟩
      refine ⟨s, hs, fun d hd => ?_⟩
      obtain ⟨s', h1, h2⟩ := hall d hd
      exact ⟨s', by rw [← e]; exact h1, h2⟩
    · rintro ⟨s, hs, hall⟩
      refine ⟨s, hs, fun d hd => ?_⟩
      obtain ⟨s', h1, h2⟩ := hall d hd
      exact ⟨s', by show y (u + d + a) = _; rw [e]; exact h1, h2⟩
  unfold checker
  by_cases h : CheckerKeeps y (u + a)
  · rw [if_pos (hk.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hk.mp h')), if_neg h]

/-- The checked configuration commutes with translations of `ℤ² × ℤᵏ`. -/
theorem checkAll_translate (x : Config k R) (w v : Site k) :
    checkAll (fun v' => x (v' + w)) v = checkAll x (v + w) := by
  unfold checkAll
  exact checker_translate (fun u' => x (u', v.2 + w.2)) w.1 v.1

/-- The quorum counts commute with translations of `ℤ² × ℤᵏ`. -/
theorem quorumCount_translate (x : Config k R) (w v : Site k) :
    quorumCount (checkAll (fun v' => x (v' + w))) v = quorumCount (checkAll x) (v + w) := by
  funext s
  unfold quorumCount
  congr 1
  refine Finset.filter_congr (fun i _ => ?_)
  rw [checkAll_translate]
  have : ((v.1, v.2 + provider k i) + w : Site k) = ((v + w).1, (v + w).2 + provider k i) :=
    Prod.ext rfl (add_right_comm _ _ _)
  rw [this]

/-- **Clause (i) of `IsPositiveRatePCA`** (Section 2.2: `F^[k]_R` is a cellular automaton): the
quorum rule commutes with every translation of `ℤ² × ℤᵏ`. -/
theorem quorumRule_translate (x : Config k R) (w : Site k) :
    quorumRule k R (fun v => x (v + w)) = fun v => quorumRule k R x (v + w) := by
  funext v
  unfold quorumRule
  rw [quorumCount_translate]

/-- **`set:def-noise` and the paragraph after `set:def-quorum`:** for `0 < ε ≤ 1` the noisy quorum
rule is a positive-rate probabilistic cellular automaton (the four clauses of
`IsPositiveRatePCA`). -/
theorem isPositiveRatePCA {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) : IsPositiveRatePCA k R ε :=
  ⟨fun w x => quorumRule_translate x w, fun _ _ _ h => quorumRule_local h,
    fun x => law_dirac_one h0.le h1 x, fun x v s => siteLaw_pos h0 x v s⟩

end FNE

end
