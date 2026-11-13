/-
# Definitions: token tables, refutability and safe sets (Sections 2.4 and 2.5)

These objects are internal to the proof (they do not occur in `cor:eight`), so the encoding is
chosen for convenience; each choice is noted. Positions and symbols of the `j` tokens are maps
`Fin j → ℤ²` and `Fin j → L_R`.
-/
import FixedNoiseErgodicity.Basic

set_option autoImplicit false

namespace FNE.TokenGame

variable {R : WangSet} {j : ℕ}

/-- `set:def-safe`. A `j`-token state `(u, s) ∈ (ℤ²)^j × L_R^j`.
`set:sub-tables` identifies a table with a set of states; we use sets of states throughout. -/
abbrev State (R : WangSet) (j : ℕ) := (Fin j → Plane) × (Fin j → LiveSymbol R)

/-- `set:def-safe` (W1), equivalently: rule (D1) of `set:def-tables` deletes nothing.
Coincident tokens carry equal symbols. -/
def Coincident (st : State R j) : Prop :=
  ∀ i i' : Fin j, st.1 i = st.1 i' → st.2 i = st.2 i'

/-- `set:def-safe`. The clone of token `i` onto token `i'`. -/
def clone (st : State R j) (i i' : Fin j) : State R j :=
  (Function.update st.1 i' (st.1 i), Function.update st.2 i' (st.2 i))

/-- `set:def-safe`. The state after token `i` moves by `d` and takes the symbol `s'`.
It is a *move of token `i` by `d`* when `s'` is compatible with `s_i` at displacement `d`. -/
def move (st : State R j) (i : Fin j) (d : Plane) (s' : LiveSymbol R) : State R j :=
  (Function.update st.1 i (st.1 i + d), Function.update st.2 i s')

/-- `set:def-safe`. A set `W` of states with positions in `V^j` is `V`-safe if it satisfies
(W1)–(W3). -/
structure IsSafe (V : Set Plane) (W : Set (State R j)) : Prop where
  /-- positions lie in `V^j` -/
  pos : ∀ st ∈ W, ∀ i, st.1 i ∈ V
  /-- (W1) -/
  coinc : ∀ st ∈ W, Coincident st
  /-- (W2) -/
  clone_mem : ∀ st ∈ W, ∀ i i', i ≠ i' → clone st i i' ∈ W
  /-- (W3) -/
  move_mem : ∀ st ∈ W, ∀ i, ∀ d ∈ mooreDirs, st.1 i + d ∈ V →
    ∃ s', Compatible (st.2 i) s' d ∧ move st i d s' ∈ W

/-- `set:def-safe`. A plane-safe set is a `ℤ²`-safe set. -/
abbrev IsPlaneSafe (W : Set (State R j)) : Prop := IsSafe Set.univ W

/-- `set:def-tables`. The table of all tuples on `V_r`. -/
def allTuples (r : ℕ) : Set (State R j) := {st | ∀ i, st.1 i ∈ box r}

/-- `set:tables`. A table is *closed* if neither (D1) nor (D3) deletes anything from it. -/
structure TableClosed (T : Set (State R j)) : Prop where
  /-- (D1) deletes nothing -/
  coinc : ∀ st ∈ T, Coincident st
  /-- (D3) deletes nothing -/
  clone_mem : ∀ st ∈ T, ∀ i i', i ≠ i' → clone st i i' ∈ T

/-- `set:def-tables`, `set:tables`(i). `Inst(S)`: the largest closed table contained in `S`.
**[choice]** The paper defines `Inst(S)` by applying (D1) and (D3) until neither applies, and
proves in `set:tables`(i) that the result is the largest closed subtable; we take that
characterization as the definition. -/
def inst (T : Set (State R j)) : Set (State R j) :=
  {st | ∃ T' ⊆ T, TableClosed T' ∧ st ∈ T'}

/-- `set:def-tables` (D2), evaluated with reference table `S` in the box `V_r`: for every
token `i` and direction `d ∈ D` with `u_i + d ∈ V_r`, some live `s'` compatible with `s_i` at
displacement `d` has the moved tuple in `S`. -/
def MoveOK (r : ℕ) (S : Set (State R j)) (st : State R j) : Prop :=
  ∀ i, ∀ d ∈ mooreDirs, st.1 i + d ∈ box r → ∃ s', Compatible (st.2 i) s' d ∧ move st i d s' ∈ S

/-- `set:def-tables`. `Timed(S)`: apply (D2) once, simultaneously, with reference `S`. -/
def timed (r : ℕ) (S : Set (State R j)) : Set (State R j) :=
  {st | st ∈ S ∧ MoveOK r S st}

/-- `set:def-tables`. The token tables `S^{(r)}_n`: `S_0 = Inst(all tuples)` and
`S_{n+1} = Inst(Timed(S_n))`. -/
def tables (R : WangSet) (j : ℕ) (r : ℕ) : ℕ → Set (State R j)
  | 0 => inst (allTuples r)
  | n + 1 => inst (timed r (tables R j r n))

/-- The position tuple `𝟎 = (0, …, 0)`. -/
def origin : Fin j → Plane := fun _ => 0

/-- `set:def-refutable`. `R` is `j`-token refutable if `S^{(r)}_τ(𝟎) = ∅` for some `r` and `τ`. -/
def Refutable (R : WangSet) (j : ℕ) : Prop :=
  ∃ r τ : ℕ, ∀ s : Fin j → LiveSymbol R, (origin, s) ∉ tables R j r τ

/-- `fgt:sec-setting`. `R` is `j`-token refutable *with time `τ`* (in the box `V_r`). -/
def RefutableWithTime (R : WangSet) (j : ℕ) (τ : ℕ) : Prop :=
  ∃ r : ℕ, ∀ s : Fin j → LiveSymbol R, (origin, s) ∉ tables R j r τ

end FNE.TokenGame
