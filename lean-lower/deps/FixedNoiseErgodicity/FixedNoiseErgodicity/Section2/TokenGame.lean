/-
# Section 2.4–2.5: tables, safe sets and the token game

Proved here:
* `set:tables` (i), (ii): `inst` is the largest closed subtable; monotonicity; `S_{n+1} ⊆ S_n`;
* `set:stable` (i) in the form used below: every `V_r`-safe set lies in every `S^{(r)}_n`, and
  the limit table `⋂ₙ S^{(r)}_n` is `V_r`-safe;
* `set:walk` for plane-safe sets;
* `set:plane` = `thm:game`(i): `R` is `j`-token refutable iff there is no nonempty plane-safe
  set of `j`-token states;
* `thm:game`(iv): a Wang set that tiles is not `j`-token refutable.

**[choice]** `set:tables`(iii) (eventual stabilization) is not needed: the limit table is the
intersection `⋂ₙ S_n`, and a pigeonhole over the finite set `L_R` replaces the stabilization.
-/
import FixedNoiseErgodicity.Defs.TokenGame

set_option autoImplicit false

open Filter

namespace FNE.TokenGame

variable {R : WangSet} {j : ℕ}

/-! ## Two pigeonhole lemmas over a finite type -/

/-- If `P n a` is antitone in `n` and every `n` has a witness, one witness serves every `n`. -/
theorem exists_forall_of_antitone {α : Type*} [Finite α] (P : ℕ → α → Prop)
    (hP : ∀ a, Antitone (fun n => P n a)) (h : ∀ n, ∃ a, P n a) : ∃ a, ∀ n, P n a := by
  by_contra hne
  push Not at hne
  choose N hN using hne
  have := Fintype.ofFinite α
  obtain ⟨a, ha⟩ := h (Finset.univ.sup N)
  exact hN a (hP a (Finset.le_sup (Finset.mem_univ a)) ha)

/-- If infinitely many `r` have a witness in a finite type, one witness serves infinitely many. -/
theorem exists_frequently_of_frequently {α : Type*} [Finite α] {P : ℕ → α → Prop}
    (h : ∃ᶠ r in atTop, ∃ a, P r a) : ∃ a, ∃ᶠ r in atTop, P r a := by
  by_contra hne
  push Not at hne
  have hall : ∀ᶠ r in atTop, ∀ a, ¬ P r a := Filter.eventually_all.mpr hne
  exact h (hall.mono fun r hr ⟨a, ha⟩ => hr a ha)

/-! ## `set:tables`: closed tables, `inst` and `timed` -/

theorem inst_subset (T : Set (State R j)) : inst T ⊆ T := by
  rintro st ⟨T', hT', -, hst⟩
  exact hT' hst

/-- `set:tables`(i): `Inst(S)` is closed. -/
theorem inst_closed (T : Set (State R j)) : TableClosed (inst T) where
  coinc := by
    rintro st ⟨T', -, hc, hst⟩
    exact hc.coinc st hst
  clone_mem := by
    rintro st ⟨T', hT', hc, hst⟩ i i' hii'
    exact ⟨T', hT', hc, hc.clone_mem st hst i i' hii'⟩

/-- `set:tables`(i): every closed subtable of `S` lies in `Inst(S)`. -/
theorem subset_inst {T T' : Set (State R j)} (h : T' ⊆ T) (hc : TableClosed T') :
    T' ⊆ inst T :=
  fun _ hst => ⟨T', h, hc, hst⟩

/-- `set:tables`(ii). -/
theorem inst_mono {T T' : Set (State R j)} (h : T ⊆ T') : inst T ⊆ inst T' :=
  subset_inst ((inst_subset T).trans h) (inst_closed T)

theorem timed_subset (r : ℕ) (S : Set (State R j)) : timed r S ⊆ S :=
  fun _ h => h.1

/-- `set:tables`(ii). -/
theorem timed_mono (r : ℕ) {S S' : Set (State R j)} (h : S ⊆ S') : timed r S ⊆ timed r S' := by
  rintro st ⟨hst, hmv⟩
  refine ⟨h hst, fun i d hd hin => ?_⟩
  obtain ⟨s', hc, hm⟩ := hmv i d hd hin
  exact ⟨s', hc, h hm⟩

theorem tables_closed (r n : ℕ) : TableClosed (tables R j r n) := by
  cases n <;> exact inst_closed _

theorem tables_zero_subset (r : ℕ) : tables R j r 0 ⊆ allTuples r :=
  inst_subset _

theorem tables_succ_subset_timed (r n : ℕ) :
    tables R j r (n + 1) ⊆ timed r (tables R j r n) :=
  inst_subset _

/-- `set:tables`(ii): `S_{n+1} ⊆ S_n`. -/
theorem tables_succ_subset (r n : ℕ) : tables R j r (n + 1) ⊆ tables R j r n := by
  induction n with
  | zero => exact (tables_succ_subset_timed r 0).trans (timed_subset _ _)
  | succ n ih => exact inst_mono (timed_mono r ih)

theorem tables_antitone (r : ℕ) : Antitone (tables R j r) :=
  antitone_nat_of_succ_le (tables_succ_subset r)

/-! ## `set:stable`(i): safe sets and the limit table -/

/-- `set:stable`(i), one half: a `V_r`-safe set lies in every table `S^{(r)}_n`. -/
theorem safe_subset_tables {r : ℕ} {W : Set (State R j)} (hW : IsSafe (box r : Set Plane) W)
    (n : ℕ) : W ⊆ tables R j r n := by
  have hc : TableClosed W := ⟨hW.coinc, hW.clone_mem⟩
  induction n with
  | zero => exact subset_inst (fun st hst => hW.pos st hst) hc
  | succ n ih =>
    refine subset_inst (fun st hst => ⟨ih hst, fun i d hd hin => ?_⟩) hc
    obtain ⟨s', hcomp, hm⟩ := hW.move_mem st hst i d hd hin
    exact ⟨s', hcomp, ih hm⟩

/-- The limit table `S^{(r)}_∞ = ⋂ₙ S^{(r)}_n`. -/
def limitTable (R : WangSet) (j r : ℕ) : Set (State R j) := ⋂ n, tables R j r n

theorem mem_limitTable {r : ℕ} {st : State R j} :
    st ∈ limitTable R j r ↔ ∀ n, st ∈ tables R j r n :=
  Set.mem_iInter

/-- `set:stable`(i), other half: the limit table is `V_r`-safe. -/
theorem limitTable_safe (r : ℕ) : IsSafe (box r : Set Plane) (limitTable R j r) where
  pos st hst := tables_zero_subset r (mem_limitTable.mp hst 0)
  coinc st hst := (tables_closed r 0).coinc st (mem_limitTable.mp hst 0)
  clone_mem st hst i i' hii' :=
    mem_limitTable.mpr fun n => (tables_closed r n).clone_mem st (mem_limitTable.mp hst n) i i' hii'
  move_mem st hst i d hd hin := by
    have hstep : ∀ n, ∃ s', Compatible (st.2 i) s' d ∧ move st i d s' ∈ tables R j r n :=
      fun n => (tables_succ_subset_timed r n (mem_limitTable.mp hst (n + 1))).2 i d hd hin
    obtain ⟨s', hs'⟩ := exists_forall_of_antitone
      (fun n s' => Compatible (st.2 i) s' d ∧ move st i d s' ∈ tables R j r n)
      (fun _ _ _ hnm h => ⟨h.1, tables_antitone r hnm h.2⟩) hstep
    exact ⟨s', (hs' 0).1, mem_limitTable.mpr fun n => (hs' n).2⟩

/-- Restricting a plane-safe set to positions in `V_r` gives a `V_r`-safe set
(proof of `set:plane`, first paragraph). -/
theorem restrict_safe {W : Set (State R j)} (hW : IsPlaneSafe W) (r : ℕ) :
    IsSafe (box r : Set Plane) {st | st ∈ W ∧ ∀ i, st.1 i ∈ box r} where
  pos st hst := hst.2
  coinc st hst := hW.coinc st hst.1
  clone_mem st hst i i' hii' := by
    refine ⟨hW.clone_mem st hst.1 i i' hii', fun l => ?_⟩
    simp only [clone, Function.update_apply]
    split_ifs
    · exact hst.2 i
    · exact hst.2 l
  move_mem st hst i d hd hin := by
    obtain ⟨s', hc, hm⟩ := hW.move_mem st hst.1 i d hd (Set.mem_univ _)
    refine ⟨s', hc, hm, fun l => ?_⟩
    simp only [move, Function.update_apply]
    split_ifs
    · exact hin
    · exact hst.2 l

/-! ## `set:walk` for plane-safe sets -/

section Walk

variable {W : Set (State R j)}

/-- Cloning token `i₀` onto every other token (proof of `set:walk`). -/
theorem cloneAll_mem {V : Set Plane} (hW : IsSafe V W) {st : State R j} (hst : st ∈ W)
    (i₀ : Fin j) : ((fun _ => st.1 i₀), (fun _ => st.2 i₀)) ∈ W := by
  classical
  have key : ∀ F : Finset (Fin j),
      ((fun i => if i ∈ F then st.1 i₀ else st.1 i),
        (fun i => if i ∈ F then st.2 i₀ else st.2 i)) ∈ W := by
    intro F
    induction F using Finset.induction_on with
    | empty => simpa using hst
    | insert a F ha ih =>
      by_cases hai : a = i₀
      · subst hai
        convert ih using 1
        ext i <;> by_cases hi : i = a <;> simp [hi]
      · have h := hW.clone_mem _ ih i₀ a (Ne.symm hai)
        convert h using 1
        ext i <;> by_cases hi : i = a <;> simp [clone, hi]
  simpa using key Finset.univ

/-- A diagonal state (all tokens on one site with one symbol) moves by one Moore step. -/
theorem diag_step (hW : IsPlaneSafe W) (i₀ : Fin j) {u : Plane} {s : LiveSymbol R}
    (h : ((fun _ => u), (fun _ => s)) ∈ W) {d : Plane} (hd : d ∈ mooreDirs) :
    ∃ s', ((fun _ => u + d), (fun _ => s')) ∈ W := by
  obtain ⟨s', -, hm⟩ := hW.move_mem _ h i₀ d hd (Set.mem_univ _)
  exact ⟨s', by simpa [move] using cloneAll_mem hW hm i₀⟩

theorem diag_to_axis1 (hW : IsPlaneSafe W) (i₀ : Fin j) (b : ℤ) :
    ∀ a : ℤ, ∀ s : LiveSymbol R, ((fun _ => ((a, b) : Plane)), (fun _ => s)) ∈ W →
      ∃ s', ((fun _ => ((0, b) : Plane)), (fun _ => s')) ∈ W := by
  intro a
  induction a using Int.induction_on with
  | zero => exact fun s h => ⟨s, h⟩
  | succ i ih =>
    intro s h
    obtain ⟨s', h'⟩ := diag_step hW i₀ h (d := (-1, 0)) (by decide)
    exact ih s' (by simpa using h')
  | pred i ih =>
    intro s h
    obtain ⟨s', h'⟩ := diag_step hW i₀ h (d := (1, 0)) (by decide)
    exact ih s' (by simpa using h')

theorem diag_to_origin (hW : IsPlaneSafe W) (i₀ : Fin j) :
    ∀ b : ℤ, ∀ s : LiveSymbol R, ((fun _ => ((0, b) : Plane)), (fun _ => s)) ∈ W →
      ∃ s', ((fun _ => ((0, 0) : Plane)), (fun _ => s')) ∈ W := by
  intro b
  induction b using Int.induction_on with
  | zero => exact fun s h => ⟨s, h⟩
  | succ i ih =>
    intro s h
    obtain ⟨s', h'⟩ := diag_step hW i₀ h (d := (0, -1)) (by decide)
    exact ih s' (by simpa using h')
  | pred i ih =>
    intro s h
    obtain ⟨s', h'⟩ := diag_step hW i₀ h (d := (0, 1)) (by decide)
    exact ih s' (by simpa using h')

/-- `set:walk` (plane case): every nonempty plane-safe set contains a state `(𝟎, s)`. -/
theorem walk (hW : IsPlaneSafe W) (hne : W.Nonempty) : ∃ s, (origin, s) ∈ W := by
  obtain ⟨st, hst⟩ := hne
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    refine ⟨st.2, ?_⟩
    convert hst using 1
    ext i <;> exact i.elim0
  · let i₀ : Fin j := ⟨0, hj⟩
    have h1 := cloneAll_mem hW hst i₀
    obtain ⟨s1, h2⟩ := diag_to_axis1 hW i₀ (st.1 i₀).2 (st.1 i₀).1 (st.2 i₀) (by simpa using h1)
    obtain ⟨s2, h3⟩ := diag_to_origin hW i₀ (st.1 i₀).2 s1 h2
    exact ⟨fun _ => s2, h3⟩

end Walk

/-! ## `set:plane` = `thm:game`(i) -/

theorem eventually_mem_box (p : Plane) : ∀ᶠ r in atTop, p ∈ box r := by
  filter_upwards [eventually_ge_atTop (p.1.natAbs + p.2.natAbs)] with r hr
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  omega

/-- `set:plane`, `thm:game`(i): `R` is `j`-token refutable if and only if there is no nonempty
plane-safe set of `j`-token states. -/
theorem refutable_iff_not_exists_planeSafe :
    Refutable R j ↔ ¬ ∃ W : Set (State R j), W.Nonempty ∧ IsPlaneSafe W := by
  constructor
  · rintro ⟨r, τ, hr⟩ ⟨W, hne, hW⟩
    obtain ⟨s, hs⟩ := walk hW hne
    have hsub := safe_subset_tables (restrict_safe hW r) τ
    refine hr s (hsub ⟨hs, fun i => ?_⟩)
    simp [origin, box]
  · intro h
    by_contra hnr
    simp only [Refutable, not_exists, not_forall, not_not] at hnr
    -- for every box, some symbol tuple at `𝟎` survives every table
    have hlim : ∀ r, ∃ s : Fin j → LiveSymbol R, (origin, s) ∈ limitTable R j r := by
      intro r
      obtain ⟨s, hs⟩ := exists_forall_of_antitone (fun n s => (origin, s) ∈ tables R j r n)
        (fun _ _ _ hnm h => tables_antitone r hnm h) (hnr r)
      exact ⟨s, mem_limitTable.mpr hs⟩
    -- the states that survive in infinitely many boxes
    let W : Set (State R j) := {st | ∃ᶠ r in atTop, st ∈ limitTable R j r}
    apply h
    refine ⟨W, ?_, ?_⟩
    · obtain ⟨s, hs⟩ := exists_frequently_of_frequently
        (P := fun r s => (origin, s) ∈ limitTable R j r)
        (Filter.Frequently.of_forall hlim)
      exact ⟨(origin, s), hs⟩
    · refine ⟨fun _ _ _ => Set.mem_univ _, ?_, ?_, ?_⟩
      · intro st hst
        obtain ⟨r, hr⟩ := hst.exists
        exact (limitTable_safe r).coinc st hr
      · intro st hst i i' hii'
        exact hst.mono fun r hr => (limitTable_safe r).clone_mem st hr i i' hii'
      · intro st hst i d hd _
        have hfr : ∃ᶠ r in atTop, ∃ s', Compatible (st.2 i) s' d ∧
            move st i d s' ∈ limitTable R j r := by
          refine (hst.and_eventually (eventually_mem_box (st.1 i + d))).mono ?_
          rintro r ⟨hr, hbox⟩
          exact (limitTable_safe r).move_mem st hr i d hd hbox
        obtain ⟨s', hs'⟩ := exists_frequently_of_frequently hfr
        obtain ⟨r, hr⟩ := hs'.exists
        exact ⟨s', hr.1, hs'.mono fun _ h => h.2⟩

/-! ## `thm:game`(iv): tilings are never refuted -/

/-- `thm:game`(iv): if `R` tiles the plane, then `R` is not `j`-token refutable. -/
theorem not_refutable_of_tiles (hR : Tiles R) : ¬ Refutable R j := by
  obtain ⟨θ, hθ⟩ := hR
  rw [refutable_iff_not_exists_planeSafe, not_not]
  classical
  refine ⟨{st | st.2 = fun i => blockConfig hθ (st.1 i)}, ⟨(origin, fun i => blockConfig hθ 0),
    by simp [origin]⟩, ⟨fun _ _ _ => Set.mem_univ _, ?_, ?_, ?_⟩⟩
  · intro st hst i i' h
    simp only [Set.mem_setOf_eq] at hst
    rw [hst]
    simp only [h]
  · intro st hst i i' _
    simp only [Set.mem_setOf_eq] at hst ⊢
    funext l
    simp only [clone, Function.update_apply]
    split_ifs <;> simp [hst]
  · intro st hst i d _ _
    simp only [Set.mem_setOf_eq] at hst
    refine ⟨blockConfig hθ (st.1 i + d), ?_, ?_⟩
    · rw [hst]; exact blockConfig_compatible hθ _ _
    · simp only [Set.mem_setOf_eq, move]
      funext l
      simp only [Function.update_apply]
      split_ifs <;> simp [hst]

end FNE.TokenGame
