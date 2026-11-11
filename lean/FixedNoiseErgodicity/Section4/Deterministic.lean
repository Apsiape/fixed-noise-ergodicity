/-
# Section 4 (memory): the deterministic part

Printed Section 4 ("Tilings give memory", source file `03-memory.tex`). Proved here, for every
realisation of the noise:
* `mem:fixed`: the checker keeps a cloned tiling wherever the nine planar neighbours agree with
  it, and `F^[k]_R(ξ) = ξ`;
* `mem:two-parents` (a) and (b);
* `mem:dominate`: every bad point of either run is marked by the domination field.
-/
import FixedNoiseErgodicity.Defs.Field

set_option autoImplicit false

namespace FNE

variable {k : ℕ} {R : WangSet}

/-! ## Providers -/

/-- At least `n` providers satisfy `p` and at most `m` do not: counting on `{0, …, k}`. -/
theorem card_filter_not_add (p : Option (Fin k) → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card + (Finset.univ.filter (fun i => ¬ p i)).card = k + 1 := by
  rw [Finset.card_filter_add_card_filter_not]
  simp

/-- Two distinct providers in a finset with more than one element. -/
theorem exists_two_of_one_lt_card {s : Finset (Option (Fin k))} (h : 1 < s.card) :
    ∃ i ∈ s, ∃ i' ∈ s, i ≠ i' := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
  exact ⟨a, ha, b, hb, hab⟩

/-! ## `mem:fixed` -/

section Fixed

variable {θ : Plane → Tile} (hθ : IsTiling R θ)

theorem zero_mem_box_one : ((0, 0) : Plane) ∈ box 1 := by decide

theorem plane_add_zero' (u : Plane) : u + ((0, 0) : Plane) = u := add_zero u

theorem mem_box_one_of_mem_mooreDirs {d : Plane} (hd : d ∈ mooreDirs) : d ∈ box 1 :=
  Finset.mem_of_mem_erase hd

/-- `mem:fixed`, first claim: if `x` agrees with the cloned tiling `ξ` at the nine sites
`(u + d, P)`, `d ∈ {-1,0,1}²`, then `(C̄x)(u, P) = ξ(u, P)`. -/
theorem checkAll_eq_cloned {x : Config k R} {u : Plane} {P : Fin k → ℤ}
    (h : ∀ d ∈ box 1, x (u + d, P) = clonedTiling k hθ (u + d, P)) :
    checkAll x (u, P) = clonedTiling k hθ (u, P) := by
  have h0 : x (u, P) = .live (blockConfig hθ u) := by
    have := h (0, 0) zero_mem_box_one
    rw [plane_add_zero'] at this
    exact this
  have hkeep : CheckerKeeps (fun u' => x (u', P)) u := by
    refine ⟨blockConfig hθ u, h0, fun d hd => ⟨blockConfig hθ (u + d), ?_, ?_⟩⟩
    · exact h d (mem_box_one_of_mem_mooreDirs hd)
    · exact blockConfig_compatible hθ u d
  show checker (fun u' => x (u', P)) u = clonedTiling k hθ (u, P)
  unfold checker
  rw [if_pos hkeep]
  exact h0

/-- `mem:fixed`, contrapositive form used in `mem:two-parents`(a). -/
theorem exists_disagree_of_checkAll_ne {x : Config k R} {u : Plane} {P : Fin k → ℤ}
    (h : checkAll x (u, P) ≠ clonedTiling k hθ (u, P)) :
    ∃ d ∈ box 1, x (u + d, P) ≠ clonedTiling k hθ (u + d, P) := by
  by_contra hne
  push Not at hne
  exact h (checkAll_eq_cloned hθ hne)

/-- The cloned tiling does not depend on the transverse coordinate. -/
theorem clonedTiling_apply (u : Plane) (P : Fin k → ℤ) :
    clonedTiling k hθ (u, P) = .live (blockConfig hθ u) := rfl

/-- `mem:fixed`, second claim: `F^[k]_R(ξ) = ξ` for `k ≥ 2`. -/
theorem quorumRule_cloned (hk : 2 ≤ k) : quorumRule k R (clonedTiling k hθ) = clonedTiling k hθ := by
  funext v
  obtain ⟨u, P⟩ := v
  rw [clonedTiling_apply, quorumRule_eq_live_iff hk]
  have hall : ∀ i : Option (Fin k),
      checkAll (clonedTiling k hθ) (u, P + provider k i) = .live (blockConfig hθ u) := by
    intro i
    rw [checkAll_eq_cloned hθ (fun d _ => rfl)]
    rfl
  unfold quorumCount
  simp only [hall, Finset.filter_true, Finset.card_univ, Fintype.card_option, Fintype.card_fin]
  omega

end Fixed

/-! ## Live outputs need live inputs -/

/-- If a non-event site carries the live symbol `s` at time `t + 1`, then at least `k` providers
carry `s` at time `t` (the checker keeps only its centre). This is `mem:two-parents`(b) before
the count, and Step 2 of `fgt:transport`. -/
theorem providers_of_live (hk : 2 ≤ k) (x : Config k R) (ω : Noise k R) (t : ℕ) (v : Site k)
    (s : LiveSymbol R) (hlive : run x ω (t + 1) v = .live s) (hev : (ω (t, v)).1 = false) :
    k ≤ (Finset.univ.filter
      (fun i : Option (Fin k) => run x ω t (v.1, v.2 + provider k i) = .live s)).card := by
  rw [run_succ, if_neg (by simp [hev]), quorumRule_eq_live_iff hk] at hlive
  refine le_trans hlive (Finset.card_le_card fun i hi => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact checker_eq_live hi

/-! ## `mem:two-parents` -/

section TwoParents

variable {θ : Plane → Tile} (hθ : IsTiling R θ)

/-- `mem:two-parents`(a). Run from the cloned tiling `ξ`; a point is *bad* if `X_t(v) ≠ ξ(v)`.
A bad point at time `t + 1` that is not an event has two bad points at time `t`, at providers
`c_i ≠ c_{i'}` and planar offsets `d, d' ∈ {-1,0,1}²`. -/
theorem two_bad_parents_cloned (hk : 2 ≤ k) (ω : Noise k R) (t : ℕ) (v : Site k)
    (hbad : run (clonedTiling k hθ) ω (t + 1) v ≠ clonedTiling k hθ v)
    (hev : (ω (t, v)).1 = false) :
    ∃ i i' : Option (Fin k), i ≠ i' ∧ ∃ d ∈ box 1, ∃ d' ∈ box 1,
      run (clonedTiling k hθ) ω t (v.1 + d, v.2 + provider k i) ≠
          clonedTiling k hθ (v.1 + d, v.2 + provider k i) ∧
      run (clonedTiling k hθ) ω t (v.1 + d', v.2 + provider k i') ≠
          clonedTiling k hθ (v.1 + d', v.2 + provider k i') := by
  classical
  set x := run (clonedTiling k hθ) ω t with hx
  obtain ⟨u, P⟩ := v
  rw [run_succ, if_neg (by simp [hev]), ← hx, clonedTiling_apply] at hbad
  -- fewer than `k` providers read the tiling symbol
  have hlt : quorumCount (checkAll x) (u, P) (.live (blockConfig hθ u)) < k := by
    by_contra hge
    exact hbad ((quorumRule_eq_live_iff hk x (u, P) _).mpr (not_lt.mp hge))
  -- so at least two providers read something else
  have hcount := card_filter_not_add
    (fun i : Option (Fin k) => checkAll x (u, P + provider k i) = .live (blockConfig hθ u))
  unfold quorumCount at hlt
  have htwo : 1 < (Finset.univ.filter (fun i : Option (Fin k) =>
      ¬ checkAll x (u, P + provider k i) = .live (blockConfig hθ u))).card := by
    simp only at hcount hlt
    omega
  obtain ⟨i, hi, i', hi', hii'⟩ := exists_two_of_one_lt_card htwo
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
  obtain ⟨d, hd, hdne⟩ := exists_disagree_of_checkAll_ne hθ (x := x) (u := u)
    (P := P + provider k i) (by rw [clonedTiling_apply]; exact hi)
  obtain ⟨d', hd', hdne'⟩ := exists_disagree_of_checkAll_ne hθ (x := x) (u := u)
    (P := P + provider k i') (by rw [clonedTiling_apply]; exact hi')
  exact ⟨i, i', hii', d, hd, d', hd', hdne, hdne'⟩

/-- `mem:two-parents`(b). Run from `⊥`; a point is *bad* if `Y_t(v)` is live. A bad point at
time `t + 1` that is not an event has two bad points at time `t`, at providers `c_i ≠ c_{i'}`
and offset `0` (both carry its symbol). -/
theorem two_bad_parents_bot (hk : 2 ≤ k) (ω : Noise k R) (t : ℕ) (v : Site k)
    (s : LiveSymbol R) (hbad : run (fun _ => .bot) ω (t + 1) v = .live s)
    (hev : (ω (t, v)).1 = false) :
    ∃ i i' : Option (Fin k), i ≠ i' ∧
      run (fun _ => .bot) ω t (v.1, v.2 + provider k i) = .live s ∧
      run (fun _ => .bot) ω t (v.1, v.2 + provider k i') = .live s := by
  have h := providers_of_live hk _ ω t v s hbad hev
  obtain ⟨i, hi, i', hi', hii'⟩ := exists_two_of_one_lt_card (lt_of_lt_of_le (by omega) h)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
  exact ⟨i, i', hii', hi, hi'⟩

end TwoParents

/-! ## `mem:dominate` -/

section Dominate

variable {θ : Plane → Tile} (hθ : IsTiling R θ)

/-- `mem:dominate`, run from the cloned tiling: every bad point has `E = 1`. -/
theorem dominate_cloned (hk : 2 ≤ k) (ω : Noise k R) :
    ∀ (t : ℕ) (v : Site k), run (clonedTiling k hθ) ω t v ≠ clonedTiling k hθ v →
      domField ω.flags t v := by
  intro t
  induction t with
  | zero => intro v h; exact absurd rfl h
  | succ t ih =>
    intro v hbad
    rw [domField_succ]
    by_cases hev : (ω (t, v)).1 = true
    · exact Or.inl hev
    · obtain ⟨i, i', hii', d, hd, d', hd', h1, h2⟩ :=
        two_bad_parents_cloned hθ hk ω t v hbad (by simpa using hev)
      exact Or.inr ⟨i, i', hii', d, hd, d', hd', ih _ h1, ih _ h2⟩

/-- `mem:dominate`, run from `⊥`: every bad (live) point has `E = 1`. -/
theorem dominate_bot (hk : 2 ≤ k) (ω : Noise k R) :
    ∀ (t : ℕ) (v : Site k) (s : LiveSymbol R), run (fun _ => .bot) ω t v = .live s →
      domField ω.flags t v := by
  intro t
  induction t with
  | zero => intro v s h; cases h
  | succ t ih =>
    intro v s hbad
    rw [domField_succ]
    by_cases hev : (ω (t, v)).1 = true
    · exact Or.inl hev
    · obtain ⟨i, i', hii', h1, h2⟩ := two_bad_parents_bot hk ω t v s hbad (by simpa using hev)
      refine Or.inr ⟨i, i', hii', (0, 0), zero_mem_box_one, (0, 0), zero_mem_box_one, ?_, ?_⟩
      · exact ih _ s (by rw [plane_add_zero']; exact h1)
      · exact ih _ s (by rw [plane_add_zero']; exact h2)

end Dominate

end FNE
