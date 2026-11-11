/-
# The data format of the corner-lemma certificate (design only)

The certificate of `thr:corner` (`BLUEPRINT.md`, Part E) is not started. This file fixes the
format it will use, on top of the tables of `Scaffold/Tables.lean` and the codes of
`Scaffold/WangSet.lean`, and proves the specification of each piece:
* letters are indices `i : Fin 276` into `Letter.letters` (`letterAt`, a bijection onto `𝔸`);
* `thr:def-lists`: the four directions `±e₁, ±e₂` (`Dir`) and the fit relation `Letter.Fits`,
  defined literally ("the pattern with `𝔞` at `0` and `𝔟` at `e` is legal") and computed by the
  colour codes (`fitCode_iff`);
* sets of letters are 276-bit masks (`letterMask p`, bit `i` is `p (letterAt i)`), and the
  letters fitting `𝔞` in direction `d` form the mask `fitMask d 𝔞`. The kernel accelerates
  `Nat.land`, `Nat.lor` and comparisons on such numbers.
Kernel checks over letters are Boolean folds (see the header of `Scaffold/Tables.lean`).
-/
import FixedNoiseErgodicity.Scaffold.WangSet
import Mathlib.Data.Nat.Bits

set_option autoImplicit false

set_option maxRecDepth 20000

namespace FNE.Scaffold

/-! ## Letters as indices -/

/-- The `i`-th letter of `𝔸`, in the order of `Letter.letters`. -/
def letterAt (i : Fin 276) : Letter :=
  Letter.letters[i.1]'(by rw [Letter.letters_length]; exact i.2)

theorem letterAt_inA (i : Fin 276) : (letterAt i).InA :=
  Letter.mem_letters.1 (List.getElem_mem _)

theorem exists_letterAt {x : Letter} (hx : x.InA) : ∃ i, letterAt i = x := by
  obtain ⟨i, hi, h⟩ := List.getElem_of_mem (Letter.mem_letters.2 hx)
  exact ⟨⟨i, Letter.letters_length ▸ hi⟩, h⟩

theorem letterAt_injective : Function.Injective letterAt := fun _ _ h =>
  Fin.ext ((Letter.letters_nodup.getElem_inj_iff).1 h)

/-! ## Directions and the fit relation (`thr:def-lists`) -/

/-- `thr:def-lists`: the four directions `e₁, -e₁, e₂, -e₂`. -/
inductive Dir where
  | e1 | e1' | e2 | e2'
  deriving DecidableEq, Repr

/-- The displacement of a direction (`e1'` is `-e₁`, `e2'` is `-e₂`). -/
def Dir.vec : Dir → Plane
  | .e1 => (1, 0) | .e1' => (-1, 0) | .e2 => (0, 1) | .e2' => (0, -1)

/-- All four directions. -/
def Dir.all : List Dir := [.e1, .e1', .e2, .e2']

/-- `thr:def-lists`: letters `𝔞, 𝔟` *fit in direction `e`* if the pattern with `𝔞` at `0` and
`𝔟` at `e` is legal. -/
def Letter.Fits (d : Dir) (a b : Letter) : Prop :=
  LegalOn Letter.MatchE Letter.MatchN {0, d.vec} (fun u => if u = 0 then a else b)

/-- `thr:def-lists` (the remark after it): `𝔞, 𝔟` fit in direction `e₁` iff they match in
direction `e₁`, and in direction `-e₁` iff `𝔟, 𝔞` match in direction `e₁`; the same for `e₂`. -/
theorem Letter.fits_iff (d : Dir) (a b : Letter) : a.Fits d b ↔
    match d with
    | .e1 => a.MatchE b
    | .e1' => b.MatchE a
    | .e2 => a.MatchN b
    | .e2' => b.MatchN a := by
  cases d <;>
    simp only [Letter.Fits, LegalOn, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq, Dir.vec] <;>
    norm_num [Prod.ext_iff]

/-- The fit relation computed by the colour codes. -/
def fitCode : Dir → Letter → Letter → Bool
  | .e1, a, b => a.codeE == b.codeW
  | .e1', a, b => b.codeE == a.codeW
  | .e2, a, b => a.codeN == b.codeS
  | .e2', a, b => b.codeN == a.codeS

theorem fitCode_iff (d : Dir) (a b : Letter) : fitCode d a b = true ↔ a.Fits d b := by
  rw [Letter.fits_iff]
  cases d <;> simp [fitCode, Letter.codeE_eq_codeW_iff, Letter.codeN_eq_codeS_iff]

/-! ## Sets of letters as 276-bit masks -/

/-- The mask of a predicate along a list: bit `i` is `p l[i]`. -/
def listMask {α : Type*} (p : α → Bool) : List α → ℕ
  | [] => 0
  | x :: l => Nat.bit (p x) (listMask p l)

theorem testBit_listMask {α : Type*} (p : α → Bool) (l : List α) (i : ℕ) (hi : i < l.length) :
    (listMask p l).testBit i = p l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    cases i with
    | zero => simp [listMask]
    | succ i =>
      simp only [listMask, Nat.testBit_bit_succ, List.getElem_cons_succ]
      exact ih i (by simpa using hi)

theorem listMask_eq_zero_iff {α : Type*} (p : α → Bool) (l : List α) :
    listMask p l = 0 ↔ ∀ x ∈ l, p x = false := by
  induction l with
  | nil => simp [listMask]
  | cons x l ih => simp [listMask, Nat.bit_eq_zero_iff, ih, and_comm]

/-- A set of letters of `𝔸` as a 276-bit mask: bit `i` is `p (letterAt i)`. -/
def letterMask (p : Letter → Bool) : ℕ := listMask p Letter.letters

theorem testBit_letterMask (p : Letter → Bool) (i : Fin 276) :
    (letterMask p).testBit i = p (letterAt i) :=
  testBit_listMask p _ i _

theorem letterMask_eq_zero_iff (p : Letter → Bool) :
    letterMask p = 0 ↔ ∀ x, x.InA → p x = false := by
  rw [letterMask, listMask_eq_zero_iff]
  exact ⟨fun h x hx => h x (Letter.mem_letters.2 hx), fun h x hx => h x (Letter.mem_letters.1 hx)⟩

/-- The four sides of a letter, for colour classes. -/
inductive Side where
  | N | E | S | W
  deriving DecidableEq, Repr

/-- The colour code of a letter on a side. -/
def Letter.code : Side → Letter → ℕ
  | .N, x => x.codeN | .E, x => x.codeE | .S, x => x.codeS | .W, x => x.codeW

/-- The colour class of code `c` on side `s`, as a mask. There are at most 64 codes per side
(`codeV`, `codeH` are `< 64`), so at most 256 class masks. -/
def classMask (s : Side) (c : ℕ) : ℕ := letterMask fun b => b.code s == c

/-- The letters that fit `𝔞` in direction `d`, as a mask: one colour class.
**Design (measured, session 4).** The kernel caches every intermediate number, so one declaration
that builds all `4 · 276` fit masks from the definitions needs more than 4 GB, while 20 masks take
a second. The certificate will therefore read fit masks from the class masks (at most 256), stored
as literal tables and checked against `classMask` in chunks of separate declarations. -/
def fitMask (d : Dir) (a : Letter) : ℕ :=
  match d with
  | .e1 => classMask .W a.codeE
  | .e1' => classMask .E a.codeW
  | .e2 => classMask .S a.codeN
  | .e2' => classMask .N a.codeS

theorem testBit_fitMask (d : Dir) (a : Letter) (i : Fin 276) :
    (fitMask d a).testBit i = true ↔ a.Fits d (letterAt i) := by
  rw [← fitCode_iff]
  cases d <;>
  · rw [fitMask, classMask, testBit_letterMask]
    simp only [Letter.code, fitCode, beq_iff_eq]
    try exact eq_comm

end FNE.Scaffold
