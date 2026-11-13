/-
# The D1 compiler, part 1: finitely supported Mathlib `TM0` machines as list-encoded machines

Mathlib's machines `Turing.TM0.Machine Γ Λ` have arbitrary types of symbols and states and halt
when the transition function returns `none`. The project's machines (`TuringMachine`,
`Statements.lean`, decision D1) are finite tables over `ℕ`, start on a blank two-sided tape in
state `0`, and halt when they enter a listed halting state. This file compiles a `TM0` machine `M`
with a finite set `S` of states that supports it (`TM0.Supports`, Mathlib's notion: `S` contains
the start state and is closed under the transitions) and a finite alphabet, together with a
nonempty input word `w`, into a `TuringMachine`:
* **numbering.** The blank `default : Γ` gets the number `0`, every other symbol `1 + ` its index
  in `Fintype.equivFin` (`symNum`, injective); a state `q ∈ S` gets the odd number
  `2 · index + 3` (`stNum`), and `1` is the one halting state;
* **the table of `M`** (`table`). For `q ∈ S` and every symbol `a`: a move `d` becomes "write `a`,
  move `d`", a write `b` becomes "write `b`, stay", and `M q a = none` becomes "go to `1`, stay";
* **the prefix** (`pre`). The machine starts on a blank tape in state `0`; the even states
  `0, 2, …, 2(n - 1)` write the input from its last symbol to its first, moving left, and the last
  of them enters the start state of `M` without moving, so that the head ends on the first symbol
  of the input: exactly Mathlib's initial tape `Tape.mk₁ w`.

**`compile_halts`:** the compiled machine halts iff `TM0.eval M w` is defined. The proof is a
step-by-step simulation (`Rel`): a configuration of the compiled machine is related to a
configuration `⟨q, T⟩` of `M` when its state is `stNum q` and its tape, read from the head, is
`symNum ∘ T.nth`. **`primrec_mkMachine`:** for a fixed table and start state, the compiled machine
is a primitive recursive function of the numbered input word, which is what the computability of
the compiler (`Compiler/Universal.lean`) needs.
-/
import FixedNoiseErgodicity.Statements
import Mathlib.Computability.TuringMachine.PostTuringMachine

set_option autoImplicit false

noncomputable section

namespace FNE.Compiler

open Turing

/-! ## Lookup in tables -/

/-- If `(k, v)` is an entry and every entry with key `k` has value `v`, the lookup of `k` is `v`. -/
theorem lookup_eq_some {α β : Type*} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α} {v : β}
    (hmem : (k, v) ∈ l) (huniq : ∀ p ∈ l, p.1 = k → p.2 = v) : l.lookup k = some v := by
  induction l with
  | nil => simp at hmem
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : k = a
    · subst h
      simp only [List.lookup, beq_self_eq_true]
      exact congrArg some (huniq _ List.mem_cons_self rfl)
    · have hne : (k == a) = false := beq_false_of_ne h
      simp only [List.lookup, hne]
      refine ih ?_ fun p hp => huniq p (List.mem_cons_of_mem _ hp)
      rcases List.mem_cons.1 hmem with h' | h'
      · exact absurd (congrArg Prod.fst h') h
      · exact h'

/-! ## Numbering of symbols and states -/

section Numbering

variable {Γ Λ : Type*} [Inhabited Γ]

open Classical in
/-- The number of a symbol: the blank `default` is `0`, every other symbol is `1 +` its index. -/
def symNum [Fintype Γ] (a : Γ) : ℕ :=
  if a = default then 0 else (Fintype.equivFin Γ a : ℕ) + 1

theorem symNum_default [Fintype Γ] : symNum (default : Γ) = 0 := by
  simp [symNum]

theorem symNum_injective [Fintype Γ] : Function.Injective (symNum : Γ → ℕ) := by
  intro a b h
  unfold symNum at h
  by_cases ha : a = default <;> by_cases hb : b = default
  · rw [ha, hb]
  · simp [ha, hb] at h
  · simp [ha, hb] at h
  · simp only [ha, hb, if_false, add_left_inj] at h
    exact (Fintype.equivFin Γ).injective (Fin.ext h)

open Classical in
/-- The index of a state in a finite set of states (`0` outside it). -/
def stIdx (S : Finset Λ) (q : Λ) : ℕ :=
  if h : q ∈ S then (S.equivFin ⟨q, h⟩ : ℕ) else 0

theorem stIdx_inj {S : Finset Λ} {q q' : Λ} (hq : q ∈ S) (hq' : q' ∈ S)
    (h : stIdx S q = stIdx S q') : q = q' := by
  unfold stIdx at h
  rw [dif_pos hq, dif_pos hq'] at h
  exact congrArg Subtype.val (S.equivFin.injective (Fin.ext h))

/-- The number of a state: odd, at least `3` (`0` and the even numbers are the prefix, `1` is the
halting state). -/
def stNum (S : Finset Λ) (q : Λ) : ℕ := 2 * stIdx S q + 3

end Numbering

/-! ## The compiled machine -/

/-- Mathlib's head directions as moves. -/
def dirMove : Dir → Move
  | .left => .left
  | .right => .right

/-- The prefix that writes the reversed numbered input `r` (from `r[0]`, moving left) and enters
`q₀` on its last write, without moving. -/
def pre (r : List ℕ) (q₀ : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ × Move)) :=
  (List.range r.length).map fun i =>
    ((2 * i, 0), (if i + 1 < r.length then 2 * i + 2 else q₀, r.getD i 0,
      if i + 1 < r.length then Move.left else Move.stay))

/-- The list-encoded machine with the prefix for the numbered input `ns`, start state `q₀` of the
simulated machine, and table `T`; the halting state is `1`. -/
def mkMachine (ns : List ℕ) (q₀ : ℕ) (T : List ((ℕ × ℕ) × (ℕ × ℕ × Move))) : TuringMachine :=
  ⟨pre ns.reverse q₀ ++ T, [1]⟩

section Compile

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Fintype Γ]

/-- The entry of the table for state `q` reading `a`. -/
def entry (M : TM0.Machine Γ Λ) (S : Finset Λ) (q : Λ) (a : Γ) :
    (ℕ × ℕ) × (ℕ × ℕ × Move) :=
  ((stNum S q, symNum a), match M q a with
    | none => (1, symNum a, .stay)
    | some (q', .move d) => (stNum S q', symNum a, dirMove d)
    | some (q', .write b) => (stNum S q', symNum b, .stay))

/-- The table of `M` on the states of `S` and all symbols. -/
def table (M : TM0.Machine Γ Λ) (S : Finset Λ) : List ((ℕ × ℕ) × (ℕ × ℕ × Move)) :=
  S.toList.flatMap fun q => (Finset.univ : Finset Γ).toList.map fun a => entry M S q a

/-- **The compiled machine** of `M` (supported on `S`) on input `w`. -/
def compile (M : TM0.Machine Γ Λ) (S : Finset Λ) (w : List Γ) : TuringMachine :=
  mkMachine (w.map symNum) (stNum S default) (table M S)

theorem table_key (M : TM0.Machine Γ Λ) (S : Finset Λ) {p : (ℕ × ℕ) × (ℕ × ℕ × Move)}
    (hp : p ∈ table M S) : ∃ q ∈ S, ∃ a : Γ, p = entry M S q a := by
  simp only [table, List.mem_flatMap, Finset.mem_toList, List.mem_map, Finset.mem_univ,
    true_and] at hp
  obtain ⟨q, hq, a, rfl⟩ := hp
  exact ⟨q, hq, a, rfl⟩

theorem pre_key {r : List ℕ} {q₀ : ℕ} {p : (ℕ × ℕ) × (ℕ × ℕ × Move)} (hp : p ∈ pre r q₀) :
    ∃ i < r.length, p = ((2 * i, 0), (if i + 1 < r.length then 2 * i + 2 else q₀, r.getD i 0,
      if i + 1 < r.length then Move.left else Move.stay)) := by
  simp only [pre, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact ⟨i, hi, rfl⟩

/-- Lookup of a state of `S` in the compiled table. -/
theorem lookup_state (M : TM0.Machine Γ Λ) (S : Finset Λ) (r : List ℕ) (q₀ : ℕ) {q : Λ}
    (hq : q ∈ S) (a : Γ) :
    (pre r q₀ ++ table M S).lookup (stNum S q, symNum a) = some (entry M S q a).2 := by
  apply lookup_eq_some
  · refine List.mem_append_right _ ?_
    simp only [table, List.mem_flatMap, Finset.mem_toList, List.mem_map, Finset.mem_univ,
      true_and]
    exact ⟨q, hq, a, rfl⟩
  · intro p hp hk
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨i, -, rfl⟩ := pre_key hp
      simp only [stNum, Prod.mk.injEq] at hk
      omega
    · obtain ⟨q', hq', a', rfl⟩ := table_key M S hp
      simp only [entry, Prod.mk.injEq, stNum] at hk
      have h1 : q' = q := stIdx_inj hq' hq (by omega)
      have h2 : a' = a := symNum_injective hk.2
      subst h1 h2
      rfl

/-- Lookup of a prefix state in the compiled table. -/
theorem lookup_pre (M : TM0.Machine Γ Λ) (S : Finset Λ) (r : List ℕ) (q₀ : ℕ) {i : ℕ}
    (hi : i < r.length) :
    (pre r q₀ ++ table M S).lookup (2 * i, 0) =
      some (if i + 1 < r.length then 2 * i + 2 else q₀, r.getD i 0,
        if i + 1 < r.length then Move.left else Move.stay) := by
  apply lookup_eq_some
  · refine List.mem_append_left _ ?_
    simp only [pre, List.mem_map, List.mem_range]
    exact ⟨i, hi, rfl⟩
  · intro p hp hk
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨j, -, rfl⟩ := pre_key hp
      simp only [Prod.mk.injEq] at hk
      have : j = i := by omega
      subst this
      rfl
    · obtain ⟨q', -, a', rfl⟩ := table_key M S hp
      simp only [entry, Prod.mk.injEq, stNum] at hk
      omega

/-! ### The simulation relation -/

/-- A configuration of the compiled machine simulates the configuration `b` of `M`. -/
structure Rel (S : Finset Λ) (c : TMConfig) (b : TM0.Cfg Γ Λ) : Prop where
  mem : b.q ∈ S
  state : c.state = stNum S b.q
  tape : ∀ i : ℤ, c.tape (c.head + i) = symNum (b.Tape.nth i)

omit [Inhabited Λ] in
theorem Rel.state_ne {S : Finset Λ} {c : TMConfig} {b : TM0.Cfg Γ Λ} (h : Rel S c b) :
    c.state ∉ [1] := by
  rw [h.state, List.mem_singleton]
  unfold stNum
  omega

variable (M : TM0.Machine Γ Λ) (S : Finset Λ) (r : List ℕ) (q₀ : ℕ)

/-- One step of `M` is one step of the compiled machine. -/
theorem step_rel (hS : TM0.Supports M ↑S) {c : TMConfig} {b b' : TM0.Cfg Γ Λ}
    (h : Rel S c b) (hb : TM0.step M b = some b') :
    Rel S ((⟨pre r q₀ ++ table M S, [1]⟩ : TuringMachine).step c) b' := by
  obtain ⟨q, T⟩ := b
  have hhead : c.tape c.head = symNum T.head := by
    simpa using h.tape 0
  have hlk := lookup_state M S r q₀ h.mem T.head
  rw [← h.state, ← hhead] at hlk
  simp only [TM0.step] at hb
  rcases hM : M q T.head with _ | ⟨q', s⟩
  · rw [hM] at hb
    simp at hb
  rw [hM] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  subst hb
  have hq' : q' ∈ S := hS.2 (by rw [hM]; rfl) h.mem
  cases s with
  | move d =>
    have hv : (entry M S q T.head).2 = (stNum S q', symNum T.head, dirMove d) := by
      simp only [entry, hM]
    refine ⟨hq', ?_, ?_⟩
    · simp only [TuringMachine.step, hlk, hv]
    · intro i
      simp only [TuringMachine.step, hlk, hv]
      rw [← hhead, Function.update_eq_self]
      cases d with
      | left =>
        simp only [dirMove, Move.toInt, Tape.move_left_nth]
        rw [← h.tape (i - 1)]
        congr 1
        ring
      | right =>
        simp only [dirMove, Move.toInt, Tape.move_right_nth]
        rw [← h.tape (i + 1)]
        congr 1
        ring
  | write a =>
    have hv : (entry M S q T.head).2 = (stNum S q', symNum a, Move.stay) := by
      simp only [entry, hM]
    refine ⟨hq', ?_, ?_⟩
    · simp only [TuringMachine.step, hlk, hv]
    · intro i
      simp only [TuringMachine.step, hlk, hv, Move.toInt, add_zero, Tape.write_nth]
      by_cases hi : i = 0
      · subst hi
        show Function.update c.tape c.head (symNum a) (c.head + 0) = symNum a
        rw [Int.add_zero, Function.update_self]
      · rw [if_neg hi, Function.update_of_ne (by omega), h.tape i]

/-- When `M` halts, the compiled machine enters the halting state `1`. -/
theorem step_halt {c : TMConfig} {b : TM0.Cfg Γ Λ} (h : Rel S c b) (hb : TM0.step M b = none) :
    ((⟨pre r q₀ ++ table M S, [1]⟩ : TuringMachine).step c).state = 1 := by
  obtain ⟨q, T⟩ := b
  have hhead : c.tape c.head = symNum T.head := by
    simpa using h.tape 0
  have hlk := lookup_state M S r q₀ h.mem T.head
  rw [← h.state, ← hhead] at hlk
  simp only [TM0.step] at hb
  rcases hM : M q T.head with _ | ⟨q', s⟩
  · have hv : (entry M S q T.head).2 = (1, symNum T.head, Move.stay) := by
      simp only [entry, hM]
    simp only [TuringMachine.step, hlk, hv]
  · rw [hM] at hb
    simp at hb

/-- Runs of `M` are followed by runs of the compiled machine. -/
theorem reaches_rel (hS : TM0.Supports M ↑S) {b₀ b : TM0.Cfg Γ Λ}
    (hr : StateTransition.Reaches (TM0.step M) b₀ b) {c : TMConfig} (hc : Rel S c b₀) :
    ∃ k, Rel S ((⟨pre r q₀ ++ table M S, [1]⟩ : TuringMachine).step^[k] c) b := by
  induction hr with
  | refl => exact ⟨0, hc⟩
  | tail _ hstep ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, ?_⟩
    rw [Function.iterate_succ_apply']
    exact step_rel M S r q₀ hS hk hstep

/-! ### The prefix -/

/-- The tape after `i` steps of the prefix: `r[0], …, r[i-1]` on the cells `0, -1, …, 1 - i`. -/
def ptape (r : List ℕ) (i : ℕ) : ℤ → ℕ := fun p =>
  if p ≤ 0 ∧ -p < i then r.getD (-p).toNat 0 else 0

theorem ptape_succ (r : List ℕ) (i : ℕ) :
    Function.update (ptape r i) (-(i : ℤ)) (r.getD i 0) = ptape r (i + 1) := by
  funext p
  by_cases hp : p = -(i : ℤ)
  · subst hp
    simp [ptape]
  · rw [Function.update_of_ne hp]
    unfold ptape
    have : (p ≤ 0 ∧ -p < (i : ℤ)) ↔ (p ≤ 0 ∧ -p < ((i + 1 : ℕ) : ℤ)) := by
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    simp only [this]

theorem ptape_zero (r : List ℕ) : ptape r 0 = fun _ => 0 := by
  funext p
  simp only [ptape]
  rw [if_neg (by omega)]

/-- The first `i ≤ length` steps of the compiled machine: the prefix. -/
theorem prefix_run {i : ℕ} (hi : i < r.length) :
    (⟨pre r q₀ ++ table M S, [1]⟩ : TuringMachine).step^[i] TuringMachine.start =
      ⟨2 * i, -(i : ℤ), ptape r i⟩ := by
  induction i with
  | zero =>
    simp only [Function.iterate_zero, id, TuringMachine.start, mul_zero, CharP.cast_eq_zero,
      neg_zero, ptape_zero]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have h0 : ptape r i (-(i : ℤ)) = 0 := by
      simp only [ptape]
      rw [if_neg (by omega)]
    have hlk := lookup_pre M S r q₀ (i := i) (by omega)
    simp only [TuringMachine.step, h0, hlk, if_pos hi, Move.toInt, ptape_succ]
    congr 1
    push_cast
    ring

/-- After the prefix, the compiled machine is in the start state of `M` with the head on the first
symbol of the input. -/
theorem prefix_done (hr : r ≠ []) :
    (⟨pre r q₀ ++ table M S, [1]⟩ : TuringMachine).step^[r.length] TuringMachine.start =
      ⟨q₀, -((r.length - 1 : ℕ) : ℤ), ptape r r.length⟩ := by
  have hn : 0 < r.length := List.length_pos_iff.2 hr
  obtain ⟨n, hn'⟩ : ∃ n, r.length = n + 1 := ⟨r.length - 1, by omega⟩
  rw [hn', Function.iterate_succ_apply', prefix_run M S r q₀ (by omega)]
  have h0 : ptape r n (-(n : ℤ)) = 0 := by
    simp only [ptape]
    rw [if_neg (by omega)]
  have hlk := lookup_pre M S r q₀ (i := n) (by omega)
  have hlt : ¬ (n + 1 < r.length) := by omega
  simp only [TuringMachine.step, h0, hlk, if_neg hlt, Move.toInt, add_zero, ptape_succ]
  simp

omit [Fintype Γ] in
/-- `Tape.mk₁ w` read from its head. -/
theorem mk₁_nth (w : List Γ) (i : ℤ) :
    (Tape.mk₁ w).nth i = if 0 ≤ i then w.getI i.toNat else default := by
  rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
  · rw [if_pos (by omega), Int.toNat_natCast]
    exact Tape.mk'_nth_nat _ _ n
  · rcases n with _ | n
    · simp only [CharP.cast_eq_zero, neg_zero, le_refl, if_true, Int.toNat_zero]
      exact Tape.mk'_nth_nat _ _ 0
    · rw [if_neg (by omega)]
      show (ListBlank.mk ([] : List Γ)).nth n = default
      rw [ListBlank.nth_mk]
      rfl

/-- The configuration after the prefix simulates the initial configuration of `M`. -/
theorem rel_init (hS : TM0.Supports M ↑S) {w : List Γ} (hw : w ≠ []) :
    Rel S ((⟨pre (w.map symNum).reverse (stNum S default) ++ table M S, [1]⟩ :
      TuringMachine).step^[w.length] TuringMachine.start) (TM0.init w) := by
  have hr : (w.map symNum).reverse ≠ [] := by simpa using hw
  have hlen : (w.map symNum).reverse.length = w.length := by simp
  have := prefix_done M S (w.map symNum).reverse (stNum S default) hr
  rw [hlen] at this
  rw [this]
  refine ⟨hS.1, rfl, ?_⟩
  intro i
  simp only [TM0.init, mk₁_nth, ptape]
  have hn : 0 < w.length := List.length_pos_iff.2 hw
  by_cases hi : 0 ≤ i ∧ i < w.length
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = j := ⟨i.toNat, by omega⟩
    have hj : j < w.length := by omega
    rw [if_pos (by omega), if_pos (by omega), Int.toNat_natCast, List.getI_eq_getElem _ hj]
    have hk : (-(-((w.length - 1 : ℕ) : ℤ) + j)).toNat = w.length - 1 - j := by omega
    rw [hk, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_reverse]
    simp only [List.getElem_map, List.length_map]
    congr 2
    omega
  · rw [if_neg (by omega)]
    by_cases h0 : 0 ≤ i
    · rw [if_pos h0, List.getI_eq_default _ (by omega), symNum_default]
    · rw [if_neg h0, symNum_default]

/-- **The compiled machine halts iff `M` halts on `w`** (for a finite alphabet, a finite set of
states supporting `M`, and a nonempty input). -/
theorem compile_halts (hS : TM0.Supports M ↑S) {w : List Γ} (hw : w ≠ []) :
    (compile M S w).Halts ↔ (TM0.eval M w).Dom := by
  set N : TuringMachine := ⟨pre (w.map symNum).reverse (stNum S default) ++ table M S, [1]⟩
    with hN
  have hcomp : compile M S w = N := rfl
  have h0 := rel_init M S hS hw
  rw [← hN] at h0
  rw [hcomp]
  change (∃ n, (N.step^[n] TuringMachine.start).state ∈ N.halting) ↔
    (StateTransition.eval (TM0.step M) (TM0.init w)).Dom
  constructor
  · rintro ⟨t, ht⟩
    by_contra hD
    have hrun : ∀ k, ∃ b, StateTransition.Reaches (TM0.step M) (TM0.init w) b ∧
        Rel S (N.step^[k] (N.step^[w.length] TuringMachine.start)) b := by
      intro k
      induction k with
      | zero => exact ⟨_, Relation.ReflTransGen.refl, h0⟩
      | succ k ih =>
        obtain ⟨b, hb, hk⟩ := ih
        rcases hs : TM0.step M b with _ | b'
        · exact absurd (Part.dom_iff_mem.2 ⟨b, StateTransition.mem_eval.2 ⟨hb, hs⟩⟩) hD
        · refine ⟨b', hb.tail hs, ?_⟩
          rw [Function.iterate_succ_apply']
          exact step_rel M S _ _ hS hk hs
    by_cases htn : t < w.length
    · have hlen : (w.map symNum).reverse.length = w.length := by simp
      have := prefix_run M S (w.map symNum).reverse (stNum S default) (i := t) (by omega)
      rw [← hN] at this
      rw [this] at ht
      simp only [hN, List.mem_singleton] at ht
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, t = k + w.length := ⟨t - w.length, by omega⟩
      rw [Function.iterate_add_apply] at ht
      obtain ⟨b, -, hk⟩ := hrun k
      exact hk.state_ne ht
  · intro hD
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.1 hD
    obtain ⟨hr, hs⟩ := StateTransition.mem_eval.1 hb
    obtain ⟨k, hk⟩ := reaches_rel M S _ _ hS hr h0
    refine ⟨k + 1 + w.length, ?_⟩
    rw [Function.iterate_add_apply, Function.iterate_succ_apply', step_halt M S _ _ hk hs]
    simp [hN]

end Compile

/-! ## The compiled machine is a primitive recursive function of the numbered input -/

theorem primrec_pre (q₀ : ℕ) : Primrec fun r : List ℕ => pre r q₀ := by
  have hlt : PrimrecPred fun p : List ℕ × ℕ => p.2 + 1 < p.1.length :=
    Primrec.nat_lt.comp (Primrec.succ.comp Primrec.snd) (Primrec.list_length.comp Primrec.fst)
  have hg : Primrec fun p : List ℕ × ℕ =>
      ((2 * p.2, 0), (if p.2 + 1 < p.1.length then 2 * p.2 + 2 else q₀, p.1.getD p.2 0,
        if p.2 + 1 < p.1.length then Move.left else Move.stay)) := by
    refine Primrec.pair (Primrec.pair (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
      (Primrec.const 0)) (Primrec.pair ?_ (Primrec.pair ?_ ?_))
    · exact Primrec.ite hlt (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
        Primrec.snd) (Primrec.const 2)) (Primrec.const q₀)
    · exact (Primrec.list_getD 0).comp Primrec.fst Primrec.snd
    · exact Primrec.ite hlt (Primrec.const _) (Primrec.const _)
  exact Primrec.list_map (Primrec.list_range.comp Primrec.list_length) hg.to₂

theorem primrec_mkMachine (q₀ : ℕ) (T : List ((ℕ × ℕ) × (ℕ × ℕ × Move))) :
    Primrec fun ns : List ℕ => mkMachine ns q₀ T := by
  have h : Primrec fun ns : List ℕ =>
      TuringMachine.equivProd.symm (pre ns.reverse q₀ ++ T, [1]) :=
    Primrec.of_equiv_symm.comp (Primrec.pair (Primrec.list_append.comp
      ((primrec_pre q₀).comp Primrec.list_reverse) (Primrec.const T)) (Primrec.const [1]))
  exact h.of_eq fun ns => rfl

end FNE.Compiler
