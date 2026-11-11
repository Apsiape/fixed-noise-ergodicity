/-
# Section 6.6, "Machines" and "A cellular automaton": the one-sided machine `M°`

Resolution of the [gap] at 06:281 (decision D10): the paper calls the simulation `M ↦ M°`
"standard" and gives one sentence. Here it is constructed and verified.

* Generic one-sided machines (`OConf`, `ostep`, `orun`: cells `1, 2, …`, head on cell `1` at the
  start, a move of one cell at every step, encoded by a Boolean: `true` is right) and the
  cellular automaton of 06:283–290 (`CASym`, `next`, `caRun` = `𝒞_t`). `caRun_eq`: for `t ≤ T(M)`,
  `𝒞_t` is the configuration of the machine (the induction behind 06:290, with the one-head
  invariant), provided the head never moves left from cell `1`.
* The machine `M°` (`OState`, `OSym`, `oTr`, `oHalt`): two tracks for the two half-tapes
  (cell `x ≥ 1` holds the positions `x - 1` (upper track) and `-x` (lower track) of `M`), the
  cell-`1` marker written at the first step, and a stay of `M` (also an idle step of `M`, a pair
  without a table entry), or a change of track at cell `1`, done as a step right followed by a
  step left (`back` states).
* `Sim` (the simulation relation), `sim_step`, `oHalts_iff` (`M°` halts iff `M` halts),
  `oRun_oneSided` (the head is always on a cell `≥ 1` and never moves left from cell `1`),
  `oHalt_init` (the initial state is not halting).
* The cellular automaton of `M°` (`CA`): `CA_eq_enc`, `CA_no_halt` (no halting state ever appears
  if `M` does not halt), `CA_one_one` (the head leaves cell `1` at the first step), `CA_halt`
  (if `M` halts, `𝒞_T(x_T)` carries a halting state at a cell `1 ≤ x_T ≤ T + 1`).
* A bound `bnd M` on the states and symbols of `M` that ever occur, and the finite symbol set
  `𝒮_M` (`InS`): every `𝒞_t(x)` lies in it (`CA_inS`).
-/
import FixedNoiseErgodicity.Statements

set_option autoImplicit false

namespace FNE.Family

open FNE

/-! ## One-sided machines and their cellular automaton (generic) -/

section OneSided

variable {Q Γ : Type*}

/-- A configuration of a one-sided machine: state, head cell (cells `1, 2, …`), tape. -/
structure OConf (Q Γ : Type*) where
  /-- the state -/
  state : Q
  /-- the head cell -/
  head : ℕ
  /-- the tape -/
  tape : ℕ → Γ

variable (tr : Q → Γ → Q × Γ × Bool) (halt : Q → Bool) (q0 : Q) (blank : Γ)

/-- One step of a one-sided machine with transition function `tr q γ = (q', γ', r)`: go to `q'`,
write `γ'`, move one cell right if `r` and one cell left otherwise. -/
def ostep (c : OConf Q Γ) : OConf Q Γ :=
  ⟨(tr c.state (c.tape c.head)).1,
    if (tr c.state (c.tape c.head)).2.2 then c.head + 1 else c.head - 1,
    Function.update c.tape c.head (tr c.state (c.tape c.head)).2.1⟩

/-- The run from the initial state on a blank tape, head on cell `1`. -/
def orun (n : ℕ) : OConf Q Γ := (ostep tr)^[n] ⟨q0, 1, fun _ => blank⟩

theorem orun_zero : orun tr q0 blank 0 = ⟨q0, 1, fun _ => blank⟩ := rfl

theorem orun_succ (n : ℕ) : orun tr q0 blank (n + 1) = ostep tr (orun tr q0 blank n) :=
  Function.iterate_succ_apply' _ _ _

/-- 06:283: the symbols `𝒮_M = Γ ∪ (𝖰 × Γ) ∪ {𝗐}` of the cellular automaton. -/
inductive CASym (Q Γ : Type*) where
  /-- the wall `𝗐` at cell `0` -/
  | wall
  /-- a tape symbol -/
  | tape (γ : Γ)
  /-- the head cell: state and scanned symbol -/
  | head (q : Q) (γ : Γ)
  deriving DecidableEq

/-- The state that the left neighbour `a` sends into the cell (a nonhalting head moving right). -/
def fromLeft : CASym Q Γ → Option Q
  | .head q γ => if !halt q && (tr q γ).2.2 then some (tr q γ).1 else none
  | _ => none

/-- The state that the right neighbour `c` sends into the cell (a nonhalting head moving left). -/
def fromRight : CASym Q Γ → Option Q
  | .head q γ => if !halt q && !(tr q γ).2.2 then some (tr q γ).1 else none
  | _ => none

/-- 06:283–288: the local rule `next(a, b, c)`. The wall stays; a nonhalting head cell writes; a
tape cell receives the head from the left neighbour if it moves right, otherwise from the right
neighbour if it moves left; in all other cases the cell keeps its symbol. -/
def next (a b c : CASym Q Γ) : CASym Q Γ :=
  match b with
  | .wall => .wall
  | .head q γ => if halt q then .head q γ else .tape (tr q γ).2.1
  | .tape γ =>
    match fromLeft tr halt a, fromRight tr halt c with
    | some q, _ => .head q γ
    | none, some q => .head q γ
    | none, none => .tape γ

/-- 06:289: `𝒞_t(0) = 𝗐`, `𝒞_0(1) = (𝗊₀, ⊔)`, `𝒞_0(x) = ⊔` for `x ≥ 2`, and
`𝒞_{t+1}(x) = next(𝒞_t(x-1), 𝒞_t(x), 𝒞_t(x+1))` for `x ≥ 1`. -/
def caRun : ℕ → ℕ → CASym Q Γ
  | _, 0 => .wall
  | 0, 1 => .head q0 blank
  | 0, _ + 2 => .tape blank
  | t + 1, x + 1 => next tr halt (caRun t x) (caRun t (x + 1)) (caRun t (x + 2))

/-- The cellular-automaton picture of a configuration: the wall at cell `0`, the pair of the state
and the scanned symbol at the head cell, the symbol elsewhere. -/
def enc (c : OConf Q Γ) (x : ℕ) : CASym Q Γ :=
  if x = 0 then .wall else if x = c.head then .head c.state (c.tape x) else .tape (c.tape x)

variable {tr halt}

theorem enc_of_ne (c : OConf Q Γ) {x : ℕ} (h0 : x ≠ 0) (hh : x ≠ c.head) :
    enc c x = .tape (c.tape x) := by
  simp [enc, h0, hh]

theorem enc_of_eq (c : OConf Q Γ) {x : ℕ} (h0 : x ≠ 0) (hh : x = c.head) :
    enc c x = .head c.state (c.tape x) := by
  unfold enc; rw [if_neg h0, if_pos hh]

theorem fromLeft_enc (c : OConf Q Γ) {x : ℕ} (hh : x ≠ c.head) :
    fromLeft tr halt (enc c x) = none := by
  unfold enc; split_ifs <;> rfl

theorem fromRight_enc (c : OConf Q Γ) {x : ℕ} (hh : x ≠ c.head) :
    fromRight tr halt (enc c x) = none := by
  unfold enc; split_ifs <;> rfl

theorem next_tape_left {a c : CASym Q Γ} {γ : Γ} {q : Q} (h : fromLeft tr halt a = some q) :
    next tr halt a (.tape γ) c = .head q γ := by
  simp [next, h]

theorem next_tape_right {a c : CASym Q Γ} {γ : Γ} {q : Q} (h : fromLeft tr halt a = none)
    (h' : fromRight tr halt c = some q) : next tr halt a (.tape γ) c = .head q γ := by
  simp [next, h, h']

theorem next_tape_none {a c : CASym Q Γ} {γ : Γ} (h : fromLeft tr halt a = none)
    (h' : fromRight tr halt c = none) : next tr halt a (.tape γ) c = .tape γ := by
  simp [next, h, h']

/-- 06:290, one step: in a configuration with one head on a cell `≥ 1`, in a nonhalting state,
that does not move left from cell `1`, the head cell writes, the neighbour in the direction of the
move receives the head, and every other cell keeps its symbol. -/
theorem next_enc (c : OConf Q Γ) (hh : 1 ≤ c.head)
    (hl : c.head = 1 → (tr c.state (c.tape c.head)).2.2 = true) (hq : halt c.state = false)
    (x : ℕ) :
    next tr halt (enc c x) (enc c (x + 1)) (enc c (x + 2)) = enc (ostep tr c) (x + 1) := by
  obtain ⟨q, h, τ⟩ := c
  simp only at hh hl hq
  rcases ho : tr q (τ h) with ⟨q', γ', r⟩
  rw [ho] at hl
  have hst : ostep tr ⟨q, h, τ⟩ =
      ⟨q', if r = true then h + 1 else h - 1, Function.update τ h γ'⟩ := by
    simp [ostep, ho]
  rw [hst]
  obtain ⟨nh, hnh⟩ : ∃ nh, nh = (if r = true then h + 1 else h - 1) := ⟨_, rfl⟩
  rw [← hnh]
  have hnew : nh ≠ h := by subst hnh; cases r <;> simp <;> omega
  by_cases hx : x + 1 = h
  · subst hx
    rw [enc_of_eq ⟨q, x + 1, τ⟩ (Nat.succ_ne_zero x) rfl,
      enc_of_ne ⟨q', nh, Function.update τ (x + 1) γ'⟩ (Nat.succ_ne_zero x) (Ne.symm hnew)]
    simp [next, hq, ho]
  · rw [enc_of_ne ⟨q, h, τ⟩ (Nat.succ_ne_zero x) hx]
    by_cases hxl : x = h
    · subst hxl
      have hx0 : x ≠ 0 := by omega
      have hl1 : fromLeft tr halt (enc ⟨q, x, τ⟩ x) = if r = true then some q' else none := by
        rw [enc_of_eq ⟨q, x, τ⟩ hx0 rfl]
        cases r <;> simp [fromLeft, hq, ho]
      have hr1 : fromRight tr halt (enc ⟨q, x, τ⟩ (x + 2)) = none :=
        fromRight_enc ⟨q, x, τ⟩ (show x + 2 ≠ x by omega)
      cases r
      · simp only [Bool.false_eq_true, if_false] at hnh hl1
        rw [next_tape_none hl1 hr1,
          enc_of_ne ⟨q', nh, Function.update τ x γ'⟩ (Nat.succ_ne_zero x) (by simp; omega)]
        simp
      · simp only [if_true] at hnh hl1
        rw [next_tape_left hl1,
          enc_of_eq ⟨q', nh, Function.update τ x γ'⟩ (Nat.succ_ne_zero x) (by simp; omega)]
        simp
    · have hl1 := fromLeft_enc (tr := tr) (halt := halt) ⟨q, h, τ⟩ hxl
      by_cases hxr : x + 2 = h
      · subst hxr
        have hr1 : fromRight tr halt (enc ⟨q, x + 2, τ⟩ (x + 2)) =
            if r = true then none else some q' := by
          rw [enc_of_eq ⟨q, x + 2, τ⟩ (Nat.succ_ne_zero _) rfl]
          cases r <;> simp [fromRight, hq, ho]
        cases r
        · simp only [Bool.false_eq_true, if_false] at hnh hr1
          rw [next_tape_right hl1 hr1,
            enc_of_eq ⟨q', nh, Function.update τ (x + 2) γ'⟩ (Nat.succ_ne_zero x) (by simp; omega)]
          simp
        · simp only [if_true] at hnh hr1
          rw [next_tape_none hl1 hr1,
            enc_of_ne ⟨q', nh, Function.update τ (x + 2) γ'⟩ (Nat.succ_ne_zero x) (by simp; omega)]
          simp
      · have hr1 := fromRight_enc (tr := tr) (halt := halt) ⟨q, h, τ⟩ hxr
        have : x + 1 ≠ nh := by
          subst hnh
          cases r
          · simp only [Bool.false_eq_true, if_false]
            rcases Nat.lt_or_ge 1 h with h1 | h1
            · omega
            · have := hl (by omega); cases this
          · simp only [if_true]; omega
        rw [next_tape_none hl1 hr1,
          enc_of_ne ⟨q', nh, Function.update τ h γ'⟩ (Nat.succ_ne_zero x) this]
        simp [Function.update_of_ne hx]

/-- 06:290: for `t ≤ T(M)`, `𝒞_t` is the configuration of the machine at time `t`, provided that
before `t` the machine is in a nonhalting state, on a cell `≥ 1`, and does not move left from
cell `1`. -/
theorem caRun_eq (n : ℕ)
    (hgood : ∀ s < n, halt (orun tr q0 blank s).state = false ∧ 1 ≤ (orun tr q0 blank s).head ∧
      ((orun tr q0 blank s).head = 1 →
        (tr (orun tr q0 blank s).state
          ((orun tr q0 blank s).tape (orun tr q0 blank s).head)).2.2 = true)) :
    ∀ x, caRun tr halt q0 blank n x = enc (orun tr q0 blank n) x := by
  induction n with
  | zero =>
    intro x
    rcases x with _ | _ | x
    · rfl
    · rfl
    · simp [caRun, enc, orun_zero]
  | succ n ih =>
    have ih := ih (fun s hs => hgood s (by omega))
    obtain ⟨hq, hh, hl⟩ := hgood n (by omega)
    intro x
    rcases x with _ | x
    · simp [caRun, enc]
    · rw [caRun, ih, ih, ih, orun_succ]
      exact next_enc _ hh hl hq x

/-- The head moves one cell per step: at time `s` it is on a cell `≤ s + 1`. -/
theorem orun_head_le (s : ℕ) : (orun tr q0 blank s).head ≤ s + 1 := by
  induction s with
  | zero => simp [orun_zero]
  | succ s ih =>
    rw [orun_succ]
    simp only [ostep]
    split_ifs <;> omega

end OneSided

/-! ## The machine `M°` -/

/-- States of `M°`: the initial state `init` (it marks cell `1`), `sim q l` (simulating `M` in
state `q`, with the head of `M` on the upper track if `l = false` and on the lower track if
`l = true`), and `back q l` (the second half of a bounce: step left and enter `sim q l`). -/
inductive OState where
  | init
  | sim (q : ℕ) (lower : Bool)
  | back (q : ℕ) (lower : Bool)
  deriving DecidableEq

/-- Tape symbols of `M°`: the cell-`1` marker and the two tracks. Cell `x ≥ 1` holds the symbols
of `M` at the positions `x - 1` (upper track) and `-x` (lower track). -/
structure OSym where
  /-- the cell-`1` marker -/
  mark : Bool
  /-- the upper track -/
  up : ℕ
  /-- the lower track -/
  lo : ℕ
  deriving DecidableEq

namespace OSym

/-- The blank of `M°`: unmarked, blank on both tracks. -/
def blank : OSym := ⟨false, 0, 0⟩

/-- The symbol on track `l` (`false`: upper, `true`: lower). -/
def get (γ : OSym) (l : Bool) : ℕ := if l then γ.lo else γ.up

/-- Write `a` on track `l`. -/
def set (γ : OSym) (l : Bool) (a : ℕ) : OSym := if l then { γ with lo := a } else { γ with up := a }

theorem set_mark (γ : OSym) (l : Bool) (a : ℕ) : (γ.set l a).mark = γ.mark := by
  cases l <;> rfl

theorem get_set (γ : OSym) (l l' : Bool) (a : ℕ) :
    (γ.set l a).get l' = if l' = l then a else γ.get l' := by
  cases l <;> cases l' <;> rfl

end OSym

/-- The move of `M°` for a move `m` of `M` on track `l`, at a cell with marker `mk`: the new track,
and `some r` for a direct move (right if `r`) or `none` for a bounce. On the upper track a cell
move is a position move; on the lower track it is the opposite move. A stay is a bounce, and so
is a change of track at cell `1` (upper track moving left, lower track moving right). -/
def oMove (l mk : Bool) : Move → Bool × Option Bool
  | .stay => (l, none)
  | .right => if l then (if mk then (false, none) else (true, some false)) else (false, some true)
  | .left => if l then (true, some true) else (if mk then (true, none) else (false, some false))

/-- **[gap] resolution, 06:281: the transition function of `M°`.** On state `init` (cell `1`):
mark the cell, step right, and come back in `sim 0 false`. On `back q l`: step left into
`sim q l`, writing back the scanned symbol. On `sim q l` reading `γ`: look up `(q, a)` with `a`
the symbol of track `l`; no entry (an idle step of `M`): bounce, unchanged; entry
`(q', a', m)`: write `a'` on track `l`, then move as `oMove` says, entering `sim q' l'` (direct
move) or `back q' l'` (bounce). -/
def oTr (M : TuringMachine) : OState → OSym → OState × OSym × Bool
  | .init, γ => (.back 0 false, { γ with mark := true }, true)
  | .back q l, γ => (.sim q l, γ, false)
  | .sim q l, γ =>
    match M.table.lookup (q, γ.get l) with
    | none => (.back q l, γ, true)
    | some (q', a', m) =>
      match oMove l γ.mark m with
      | (l', none) => (.back q' l', γ.set l a', true)
      | (l', some r) => (.sim q' l', γ.set l a', r)

/-- The halting states of `M°`: `sim q l` with `q` a halting state of `M`. -/
def oHalt (M : TuringMachine) : OState → Bool
  | .sim q _ => decide (q ∈ M.halting)
  | _ => false

/-- The initial state of `M°` is not halting. -/
theorem oHalt_init (M : TuringMachine) : oHalt M .init = false := rfl

/-- The run of `M°`. -/
abbrev oRun (M : TuringMachine) (n : ℕ) : OConf OState OSym := orun (oTr M) .init OSym.blank n

/-! ### The simulation relation -/

/-- The track of a position `p` of `M`: lower iff `p < 0`. -/
def trk (p : ℤ) : Bool := decide (p < 0)

/-- The cell of `M°` holding the position `p` of `M`. -/
def cellOf (p : ℤ) : ℕ := if p < 0 then (-p).toNat else (p + 1).toNat

/-- The position of `M` on track `l` at cell `x`. -/
def pos (l : Bool) (x : ℕ) : ℤ := if l then -(x : ℤ) else (x : ℤ) - 1

theorem cellOf_cast (p : ℤ) : (cellOf p : ℤ) = if p < 0 then -p else p + 1 := by
  unfold cellOf; split_ifs with h
  · exact Int.toNat_of_nonneg (by omega)
  · exact Int.toNat_of_nonneg (by omega)

theorem pos_trk_cellOf (p : ℤ) : pos (trk p) (cellOf p) = p := by
  unfold pos trk cellOf
  by_cases h : p < 0 <;> simp [h] <;> omega

theorem one_le_cellOf (p : ℤ) : 1 ≤ cellOf p := by
  unfold cellOf; split_ifs <;> omega

theorem pos_inj {l l' : Bool} {x x' : ℕ} (hx : 1 ≤ x) (hx' : 1 ≤ x') (h : pos l x = pos l' x') :
    l = l' ∧ x = x' := by
  unfold pos at h
  cases l <;> cases l' <;> simp at h ⊢ <;> omega

/-- The simulation relation: `M°` is in `sim q l` with `q` the state of `M` and `l` the track of
its head, on the cell of the head of `M`; cell `1` (only) is marked; and each track holds the
corresponding half-tape of `M`. -/
def Sim (c : TMConfig) (o : OConf OState OSym) : Prop :=
  o.state = .sim c.state (trk c.head) ∧ o.head = cellOf c.head ∧
    ∀ x : ℕ, 1 ≤ x → (o.tape x).mark = decide (x = 1) ∧ ∀ l, (o.tape x).get l = c.tape (pos l x)

/-- A `back` state. -/
def IsBack : OState → Prop
  | .back _ _ => True
  | _ => False

/-- Writing `a` on track `l` at the cell `h` of `M°` simulates writing `a` at the position
`pos l h` of `M`. -/
theorem tape_write {τ : ℕ → OSym} {t : ℤ → ℕ}
    (hτ : ∀ x : ℕ, 1 ≤ x → (τ x).mark = decide (x = 1) ∧ ∀ l, (τ x).get l = t (pos l x))
    {h : ℕ} (hh : 1 ≤ h) (l : Bool) (a : ℕ) :
    ∀ x : ℕ, 1 ≤ x → ((Function.update τ h ((τ h).set l a)) x).mark = decide (x = 1) ∧
      ∀ l', ((Function.update τ h ((τ h).set l a)) x).get l' =
        Function.update t (pos l h) a (pos l' x) := by
  intro x hx
  by_cases hxh : x = h
  · subst hxh
    refine ⟨by rw [Function.update_self, OSym.set_mark]; exact (hτ x hx).1, fun l' => ?_⟩
    rw [Function.update_self, OSym.get_set]
    by_cases hl : l' = l
    · subst hl; simp
    · rw [if_neg hl, Function.update_of_ne, (hτ x hx).2]
      intro he; exact hl (pos_inj hx hx he).1
  · rw [Function.update_of_ne hxh]
    refine ⟨(hτ x hx).1, fun l' => ?_⟩
    rw [Function.update_of_ne, (hτ x hx).2]
    intro he; exact hxh (pos_inj hx hh he).2

theorem update_same {τ : ℕ → OSym} (h : ℕ) : Function.update τ h (τ h) = τ :=
  Function.update_eq_self h τ

/-- **[gap] resolution, 06:281: one step of `M` is one or two steps of `M°`.** Either one step of
`M°` simulates it (a direct move), or the first step enters a `back` state on a cell `≥ 2` and the
second step completes the simulation (a bounce). -/
theorem sim_step (M : TuringMachine) {c : TMConfig} {o : OConf OState OSym} (h : Sim c o) :
    Sim (M.step c) (ostep (oTr M) o) ∨
      (IsBack (ostep (oTr M) o).state ∧ 2 ≤ (ostep (oTr M) o).head ∧
        Sim (M.step c) (ostep (oTr M) (ostep (oTr M) o))) := by
  obtain ⟨q, p, t⟩ := c
  obtain ⟨os, oh, τ⟩ := o
  obtain ⟨hs, hh, hτ⟩ := h
  simp only at hs hh hτ
  subst hs hh
  have h1 : 1 ≤ cellOf p := one_le_cellOf p
  have hget : (τ (cellOf p)).get (trk p) = t p := by
    rw [(hτ _ h1).2, pos_trk_cellOf]
  have hmk : (τ (cellOf p)).mark = decide (cellOf p = 1) := (hτ _ h1).1
  rcases hlk : M.table.lookup (q, t p) with _ | ⟨q', a', m⟩
  · -- idle step of `M`: a bounce that changes nothing
    right
    have hstep : M.step ⟨q, p, t⟩ = ⟨q, p, t⟩ := by
      simp [TuringMachine.step, hlk]
    rw [hstep]
    simp only [ostep, oTr, hget, hlk, if_true, update_same]
    refine ⟨trivial, by omega, ?_⟩
    simp only [oTr, Bool.false_eq_true, if_false, Nat.add_sub_cancel, update_same]
    exact ⟨rfl, rfl, hτ⟩
  · have hstep : M.step ⟨q, p, t⟩ = ⟨q', p + m.toInt, Function.update t p a'⟩ := by
      simp [TuringMachine.step, hlk]
    rw [hstep]
    have hw := tape_write hτ h1 (trk p) a'
    rw [pos_trk_cellOf] at hw
    have hcase : ∀ (l' : Bool) (r : Option Bool),
        oMove (trk p) (τ (cellOf p)).mark m = (l', r) →
        (trk (p + m.toInt) = l' ∧
          (r = none → (cellOf (p + m.toInt) : ℤ) = cellOf p) ∧
          (r = some true → (cellOf (p + m.toInt) : ℤ) = cellOf p + 1) ∧
          (r = some false → (cellOf (p + m.toInt) : ℤ) = cellOf p - 1)) := by
      intro l' r hm
      rw [hmk] at hm
      have e1 := cellOf_cast p
      have e2 := cellOf_cast (p + m.toInt)
      have hone : cellOf p = 1 ↔ (p = 0 ∨ p = -1) := by
        rw [← Nat.cast_inj (R := ℤ), e1, Nat.cast_one]; split_ifs <;> omega
      simp only [hone] at hm
      unfold trk at hm ⊢
      cases m <;> by_cases hp : p < 0 <;> by_cases hc : (p = 0 ∨ p = -1) <;>
        simp only [Move.toInt] at e2 ⊢ <;>
        simp [oMove, hp, hc] at hm <;> obtain ⟨rfl, rfl⟩ := hm <;>
        split_ifs at e1 e2 <;> simp_all <;>
        first | omega | exact decide_eq_false_iff_not.mpr (by omega)
    rcases hmv : oMove (trk p) (τ (cellOf p)).mark m with ⟨l', _ | r⟩
    · -- a bounce
      obtain ⟨htl, hc0, -, -⟩ := hcase l' none hmv
      right
      simp only [ostep, oTr, hget, hlk, hmv, if_true]
      refine ⟨trivial, by omega, ?_⟩
      simp only [oTr, Bool.false_eq_true, if_false, Nat.add_sub_cancel, update_same]
      exact ⟨by rw [htl], by exact_mod_cast (hc0 rfl).symm, hw⟩
    · -- a direct move
      obtain ⟨htl, -, hcr, hcl⟩ := hcase l' (some r) hmv
      left
      simp only [ostep, oTr, hget, hlk, hmv]
      refine ⟨by rw [htl], ?_, hw⟩
      cases r
      · have := hcl rfl; simp; omega
      · have := hcr rfl; simp; omega

/-- The configuration of `M` after `n` steps from the blank tape. -/
abbrev mRun (M : TuringMachine) (n : ℕ) : TMConfig := M.step^[n] TuringMachine.start

/-- After two steps (marking cell `1` and coming back), `M°` simulates the start of `M`. -/
theorem sim_two (M : TuringMachine) : Sim (mRun M 0) (oRun M 2) := by
  refine ⟨rfl, rfl, fun x hx => ?_⟩
  simp only [oRun, orun_succ, orun_zero, ostep, oTr, if_true, Bool.false_eq_true, if_false,
    mRun, Function.iterate_zero, id, TuringMachine.start]
  by_cases h1 : x = 1
  · subst h1
    refine ⟨by simp [Function.update_apply], fun l => ?_⟩
    cases l <;> simp [Function.update_apply, OSym.get, OSym.blank]
  · refine ⟨by simp [Function.update_apply, OSym.blank, h1], fun l => ?_⟩
    cases l <;> simp [Function.update_apply, OSym.get, OSym.blank, h1]

theorem mRun_succ (M : TuringMachine) (n : ℕ) : mRun M (n + 1) = M.step (mRun M n) :=
  Function.iterate_succ_apply' _ _ _

theorem oRun_succ (M : TuringMachine) (n : ℕ) : oRun M (n + 1) = ostep (oTr M) (oRun M n) :=
  orun_succ _ _ _ n

/-- Every configuration of `M` is simulated at some time. -/
theorem exists_sim (M : TuringMachine) (n : ℕ) : ∃ t, Sim (mRun M n) (oRun M t) := by
  induction n with
  | zero => exact ⟨2, sim_two M⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    rcases sim_step M ht with h | ⟨-, -, h⟩
    · exact ⟨t + 1, by rw [mRun_succ, oRun_succ]; exact h⟩
    · exact ⟨t + 1 + 1, by rw [mRun_succ, oRun_succ, oRun_succ]; exact h⟩

/-- From time `1` on, `M°` simulates some configuration of `M`, or is in a `back` state on a cell
`≥ 2` and simulates it one step later. -/
theorem sim_or_back (M : TuringMachine) (t : ℕ) (ht : 1 ≤ t) :
    ∃ n, Sim (mRun M n) (oRun M t) ∨
      (IsBack (oRun M t).state ∧ 2 ≤ (oRun M t).head ∧ Sim (mRun M n) (oRun M (t + 1))) := by
  induction t, ht using Nat.le_induction with
  | base => exact ⟨0, Or.inr ⟨trivial, le_rfl, sim_two M⟩⟩
  | succ t ht ih =>
    obtain ⟨n, h | ⟨-, -, h⟩⟩ := ih
    · rcases sim_step M h with h' | ⟨hb, h2, h'⟩
      · exact ⟨n + 1, Or.inl (by rw [mRun_succ, oRun_succ]; exact h')⟩
      · exact ⟨n + 1, Or.inr ⟨by rw [oRun_succ]; exact hb, by rw [oRun_succ]; exact h2,
          by rw [mRun_succ, oRun_succ, oRun_succ]; exact h'⟩⟩
    · exact ⟨n, Or.inl h⟩

/-- **[gap] resolution, 06:281: `M°` halts iff `M` halts.** -/
theorem oHalts_iff (M : TuringMachine) :
    (∃ t, oHalt M (oRun M t).state = true) ↔ M.Halts := by
  constructor
  · rintro ⟨t, ht⟩
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · simp [oRun, orun_zero, oHalt] at ht
    · obtain ⟨n, h | ⟨hb, -, -⟩⟩ := sim_or_back M t hpos
      · rw [h.1] at ht
        exact ⟨n, by simpa [oHalt] using ht⟩
      · revert ht hb
        cases (oRun M t).state <;> simp [IsBack, oHalt]
  · rintro ⟨n, hn⟩
    obtain ⟨t, ht⟩ := exists_sim M n
    exact ⟨t, by rw [ht.1]; simpa [oHalt] using hn⟩

/-- In a `sim` state on the marked cell `1`, `M°` moves right. -/
theorem oTr_sim_mark (M : TuringMachine) (q : ℕ) (l : Bool) (γ : OSym) (hm : γ.mark = true) :
    (oTr M (.sim q l) γ).2.2 = true := by
  simp only [oTr]
  rcases M.table.lookup (q, γ.get l) with _ | ⟨q', a', m⟩
  · rfl
  · rw [hm]
    cases l <;> cases m <;> rfl

/-- **[gap] resolution, 06:281: `M°` is one-sided.** At every time its head is on a cell `≥ 1`,
and on cell `1` it moves right (it never moves left from cell `1`, so the head of the cellular
automaton never reaches cell `0`). -/
theorem oRun_oneSided (M : TuringMachine) (t : ℕ) :
    1 ≤ (oRun M t).head ∧ ((oRun M t).head = 1 →
      (oTr M (oRun M t).state ((oRun M t).tape (oRun M t).head)).2.2 = true) := by
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · exact ⟨le_rfl, fun _ => rfl⟩
  obtain ⟨n, h | ⟨hb, h2, -⟩⟩ := sim_or_back M t hpos
  · obtain ⟨hs, hh, hτ⟩ := h
    have h1 := one_le_cellOf (mRun M n).head
    refine ⟨hh ▸ h1, fun he => ?_⟩
    rw [hs]
    apply oTr_sim_mark
    rw [(hτ _ (by omega)).1, he]; rfl
  · exact ⟨by omega, fun he => by omega⟩

/-! ### The cellular automaton of `M°` -/

/-- 06:289: `𝒞_t(x)` for the machine `M°`. -/
abbrev CA (M : TuringMachine) (t x : ℕ) : CASym OState OSym :=
  caRun (oTr M) (oHalt M) .init OSym.blank t x

/-- 06:290: for `t ≤ T(M)`, `𝒞_t` is the configuration of `M°` at time `t`. -/
theorem CA_eq_enc (M : TuringMachine) (n : ℕ)
    (hn : ∀ s < n, oHalt M (oRun M s).state = false) (x : ℕ) :
    CA M n x = enc (oRun M n) x :=
  caRun_eq _ _ n (fun s hs => ⟨hn s hs, oRun_oneSided M s⟩) x

/-- If `M` does not halt, no `𝒞_t(x)` carries a halting state (used for (H9) in
`prop:horn`(b)). -/
theorem CA_no_halt (M : TuringMachine) (hM : ¬ M.Halts) (t x : ℕ) (q : OState) (γ : OSym)
    (h : CA M t x = .head q γ) : oHalt M q = false := by
  have hall : ∀ s, oHalt M (oRun M s).state = false := fun s => by
    by_contra hs
    exact hM ((oHalts_iff M).1 ⟨s, by simpa using hs⟩)
  rw [CA_eq_enc M t (fun s _ => hall s)] at h
  unfold enc at h
  split_ifs at h <;> cases h
  exact hall t

/-- `prop:horn` (proof of (a)): the head leaves cell `1` at the first step, so `𝒞_1(1) ∈ Γ`. -/
theorem CA_one_one (M : TuringMachine) : ∃ γ, CA M 1 1 = .tape γ := by
  rw [CA_eq_enc M 1 (fun s hs => by
    obtain rfl : s = 0 := by omega
    rfl)]
  refine ⟨{ OSym.blank with mark := true }, ?_⟩
  rw [oRun_succ]
  simp [enc, ostep, oTr, orun_zero]

/-- `prop:horn` (proof of (c)): if `M` halts, with halting time `T` (the first time `M°` is in a
halting state), the head at time `T` is at a cell `1 ≤ x_T ≤ T + 1` and `𝒞_T(x_T) = (𝗊, γ)` with
`𝗊` halting. -/
theorem CA_halt (M : TuringMachine) (T : ℕ) (hT : oHalt M (oRun M T).state = true)
    (hmin : ∀ s < T, oHalt M (oRun M s).state = false) :
    ∃ x q γ, 1 ≤ x ∧ x ≤ T + 1 ∧ CA M T x = .head q γ ∧ oHalt M q = true := by
  refine ⟨(oRun M T).head, (oRun M T).state, (oRun M T).tape (oRun M T).head,
    (oRun_oneSided M T).1, orun_head_le _ _ T, ?_, hT⟩
  rw [CA_eq_enc M T hmin]
  simp [enc, Nat.one_le_iff_ne_zero.mp (oRun_oneSided M T).1]

/-! ### The finite symbol set `𝒮_M` -/

/-- A bound on the states and symbols that `M` writes or enters: one more than every target
state and every written symbol of the table (and `> 0`, for the initial state and the blank). -/
def bnd (M : TuringMachine) : ℕ := (M.table.map fun e => max e.2.1 e.2.2.1).foldr max 0 + 1

theorem lookup_mem {α β : Type*} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α} {v : β}
    (h : l.lookup k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp at h
  | cons e l ih =>
    obtain ⟨k', v'⟩ := e
    by_cases hk : k = k'
    · subst hk
      simp only [List.lookup, beq_self_eq_true] at h
      cases h; exact List.mem_cons_self
    · have : (k == k') = false := by simpa using hk
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem lookup_lt_bnd (M : TuringMachine) {k : ℕ × ℕ} {q' a' : ℕ} {m : Move}
    (h : M.table.lookup k = some (q', a', m)) : q' < bnd M ∧ a' < bnd M := by
  have hm := le_foldr_max (List.mem_map_of_mem (f := fun e : (ℕ × ℕ) × (ℕ × ℕ × Move) =>
    max e.2.1 e.2.2.1) (lookup_mem h))
  simp only at hm
  unfold bnd
  constructor <;> omega

/-- A symbol of `M°` with both tracks below the bound. -/
def SymOK (B : ℕ) (γ : OSym) : Prop := γ.up < B ∧ γ.lo < B

/-- A state of `M°` whose state of `M` is below the bound. -/
def StOK (B : ℕ) : OState → Prop
  | .init => True
  | .sim q _ => q < B
  | .back q _ => q < B

/-- 06:283: the finite symbol set `𝒮_M` of the cellular automaton, as a predicate: the wall, and
the symbols and head pairs of `M°` below the bound `bnd M`. -/
def InS (B : ℕ) : CASym OState OSym → Prop
  | .wall => True
  | .tape γ => SymOK B γ
  | .head q γ => StOK B q ∧ SymOK B γ

theorem oTr_ok (M : TuringMachine) {q : OState} {γ : OSym} (hq : StOK (bnd M) q)
    (hγ : SymOK (bnd M) γ) :
    StOK (bnd M) (oTr M q γ).1 ∧ SymOK (bnd M) (oTr M q γ).2.1 := by
  have hpos : 0 < bnd M := Nat.succ_pos _
  cases q with
  | init => exact ⟨hpos, hγ⟩
  | back q l => exact ⟨hq, hγ⟩
  | sim q l =>
    simp only [oTr]
    rcases hlk : M.table.lookup (q, γ.get l) with _ | ⟨q', a', m⟩
    · exact ⟨hq, hγ⟩
    · obtain ⟨h1, h2⟩ := lookup_lt_bnd M hlk
      have hs : SymOK (bnd M) (γ.set l a') := by
        have := hγ.1; have := hγ.2
        cases l <;> exact ⟨by simp [OSym.set]; omega, by simp [OSym.set]; omega⟩
      dsimp only
      rcases hmv : oMove l γ.mark m with ⟨l', _ | r⟩ <;> exact ⟨h1, hs⟩

theorem next_ok (M : TuringMachine) {a b c : CASym OState OSym} (ha : InS (bnd M) a)
    (hb : InS (bnd M) b) (hc : InS (bnd M) c) : InS (bnd M) (next (oTr M) (oHalt M) a b c) := by
  cases b with
  | wall => trivial
  | head q γ =>
    simp only [next]
    split_ifs
    · exact hb
    · exact (oTr_ok M hb.1 hb.2).2
  | tape γ =>
    simp only [next]
    have hl : ∀ q, fromLeft (oTr M) (oHalt M) a = some q → StOK (bnd M) q := by
      intro q hq
      cases a with
      | head q' γ' =>
        simp only [fromLeft] at hq
        split_ifs at hq
        cases hq; exact (oTr_ok M ha.1 ha.2).1
      | _ => simp [fromLeft] at hq
    have hr : ∀ q, fromRight (oTr M) (oHalt M) c = some q → StOK (bnd M) q := by
      intro q hq
      cases c with
      | head q' γ' =>
        simp only [fromRight] at hq
        split_ifs at hq
        cases hq; exact (oTr_ok M hc.1 hc.2).1
      | _ => simp [fromRight] at hq
    rcases h1 : fromLeft (oTr M) (oHalt M) a with _ | q
    · rcases h2 : fromRight (oTr M) (oHalt M) c with _ | q
      · exact hb
      · exact ⟨hr q h2, hb⟩
    · exact ⟨hl q h1, hb⟩

/-- Every `𝒞_t(x)` lies in `𝒮_M`. -/
theorem CA_inS (M : TuringMachine) (t x : ℕ) : InS (bnd M) (CA M t x) := by
  have hpos : 0 < bnd M := Nat.succ_pos _
  induction t generalizing x with
  | zero =>
    rcases x with _ | _ | x
    · trivial
    · exact ⟨trivial, hpos, hpos⟩
    · exact ⟨hpos, hpos⟩
  | succ t ih =>
    rcases x with _ | x
    · trivial
    · have e : CA M (t + 1) (x + 1) =
          next (oTr M) (oHalt M) (CA M t x) (CA M t (x + 1)) (CA M t (x + 2)) := by
        simp only [CA]; rw [caRun]
      rw [e]
      exact next_ok M (ih x) (ih (x + 1)) (ih (x + 2))

end FNE.Family
