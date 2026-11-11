/-
# Codes for `def:family`: `Primcodable` instances and the code of a colour (Section 8)

* `Primcodable` instances for the states and tape symbols of `M°`, the symbols of its cellular
  automaton and the facts (`OState`, `OSym`, `CASym`, `Fact`), through explicit equivalences with
  options and products of `ℕ` and `Bool`. They are what `M ↦ R_M` is computable with
  (`Family/Computable.lean`).
* The code of a colour of `C_M` (`colCode`): a colour `c` (a finite set of triples `(h/v, y, F)`)
  is coded by `∑_{i ∈ code(c)} 2^i`, with `code` the `Primcodable` code of a triple; it is
  injective (`colCode_injective`). Its list form `colCodeL` (a fold that adds one bit per entry)
  computes it from any list whose set of entries is `c` (`colCodeL_eq`).

**[choice]** The tile code of `def:family` (`FTile.toTile`) pairs the code of the `𝔸^r` colour with
`colCode` of the payload colour. Until session 8 the payload colour was coded by the derived
`Encodable` instance of `Finset`; that code is injective too, but it sorts lists of codes, which
has no ready `Primrec` proof. Only injectivity of the code is used anywhere else.
-/
import FixedNoiseErgodicity.Family.Horn
import Mathlib.Combinatorics.Colex

set_option autoImplicit false

namespace FNE.Family

open FNE

/-! ## `Primcodable` instances -/

/-- `OSym ≃ Bool × ℕ × ℕ` (marker, upper track, lower track). -/
def OSym.equiv : OSym ≃ Bool × ℕ × ℕ where
  toFun γ := (γ.mark, γ.up, γ.lo)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable OSym := Primcodable.ofEquiv _ OSym.equiv

/-- `OState ≃ Option (Bool × ℕ × Bool)`: `init` is `none`, `sim q l` is `some (false, q, l)`,
`back q l` is `some (true, q, l)`. -/
def OState.equiv : OState ≃ Option (Bool × ℕ × Bool) where
  toFun
    | .init => none
    | .sim q l => some (false, q, l)
    | .back q l => some (true, q, l)
  invFun
    | none => .init
    | some (false, q, l) => .sim q l
    | some (true, q, l) => .back q l
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | ⟨_ | _, q, l⟩ <;> rfl

instance : Primcodable OState := Primcodable.ofEquiv _ OState.equiv

/-- `CASym Q Γ ≃ Option (Option Q × Γ)`: the wall is `none`, a tape symbol `γ` is
`some (none, γ)`, a head cell `(q, γ)` is `some (some q, γ)`. -/
def CASym.equiv (Q Γ : Type*) : CASym Q Γ ≃ Option (Option Q × Γ) where
  toFun
    | .wall => none
    | .tape γ => some (none, γ)
    | .head q γ => some (some q, γ)
  invFun
    | none => .wall
    | some (none, γ) => .tape γ
    | some (some q, γ) => .head q γ
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | ⟨_ | q, γ⟩ <;> rfl

instance {Q Γ : Type*} [Primcodable Q] [Primcodable Γ] : Primcodable (CASym Q Γ) :=
  Primcodable.ofEquiv _ (CASym.equiv Q Γ)

/-- `Fact ≃ Option (Option (Option MSym))`: `Seed`, `Start`, `Ray`, `P_b`. -/
def Fact.equiv : Fact ≃ Option (Option (Option MSym)) where
  toFun
    | .seed => none
    | .start => some none
    | .ray => some (some none)
    | .P b => some (some (some b))
  invFun
    | none => .seed
    | some none => .start
    | some (some none) => .ray
    | some (some (some b)) => .P b
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | _ | _ | b <;> rfl

instance : Primcodable Fact := Primcodable.ofEquiv _ Fact.equiv

/-! ## The code of a colour -/

/-- A triple `(h/v, y, F)` of a colour (`false` is `h`, `true` is `v`). -/
abbrev Atom := Bool × Plane × Fact

/-- The code of a triple: its `Primcodable` code. -/
def atomCode (x : Atom) : ℕ := @Encodable.encode _ Primcodable.toEncodable x

theorem atomCode_injective : Function.Injective atomCode :=
  @Encodable.encode_injective _ Primcodable.toEncodable

/-- **[choice]** The code of a colour `c`: `∑_{i ∈ atomCode(c)} 2^i`. -/
def colCode (c : Colour) : ℕ := ∑ i ∈ c.image atomCode, 2 ^ i

/-- The code of a colour is injective (binary expansions, `Finset.geomSum_injective`). -/
theorem colCode_injective : Function.Injective colCode := fun _ _ h =>
  Finset.image_injective atomCode_injective (Finset.geomSum_injective le_rfl h)

/-- Bit `k` of `∑_{i ∈ s} 2^i` is set iff `k ∈ s`. -/
theorem bit_sum_two_pow (s : Finset ℕ) (k : ℕ) :
    (∑ i ∈ s, 2 ^ i) / 2 ^ k % 2 = 1 ↔ k ∈ s := by
  rw [← decide_eq_true_iff (p := (∑ i ∈ s, 2 ^ i) / 2 ^ k % 2 = 1),
    ← Nat.testBit_eq_decide_div_mod_eq, ← Nat.mem_bitIndices, ← List.mem_toFinset,
    Finset.toFinset_bitIndices_sum_two_pow]

/-- Set bit `k` of `n`. -/
def addBit (k n : ℕ) : ℕ := if n / 2 ^ k % 2 = 1 then n else n + 2 ^ k

/-- The code of the colour whose triples are the entries of a list. -/
def colCodeL (l : List Atom) : ℕ := l.foldr (fun x n => addBit (atomCode x) n) 0

theorem colCodeL_eq (l : List Atom) : colCodeL l = colCode l.toFinset := by
  induction l with
  | nil => simp [colCodeL, colCode]
  | cons x l ih =>
    simp only [colCodeL, List.foldr_cons] at ih ⊢
    rw [ih, List.toFinset_cons, colCode, colCode, Finset.image_insert, addBit]
    by_cases hk : atomCode x ∈ l.toFinset.image atomCode
    · rw [if_pos ((bit_sum_two_pow _ _).2 hk), Finset.insert_eq_of_mem hk]
    · rw [if_neg (fun h => hk ((bit_sum_two_pow _ _).1 h)), Finset.sum_insert hk, add_comm]

end FNE.Family
