/-
# The D1 compiler, part 2: Mathlib's codes into list-encoded machines

**`compiler : Nat.Partrec.Code → TuringMachine`**, with **`compiler_halts`**: `compiler c` halts
iff `c` halts on input `0` (`(c.eval 0).Dom`), and **`computable_compiler`**: `compiler` is
computable (even primitive recursive) in Mathlib's sense.

The route avoids a translation of codes. Every step below is a theorem of Mathlib, except the two
compilation steps of this project (`Compiler/TM0.lean` and the input numbering here):
1. **A universal code.** The partial function `n ↦ eval (ofNat Code n) 0` is partial recursive
   (`Nat.Partrec.Code.eval_part`), hence `Nat.Partrec'` (`Nat.Partrec'.part_iff₁`), hence computed
   by one code `univCode` of Mathlib's sequential model `Turing.ToPartrec.Code`
   (`Turing.ToPartrec.Code.exists_code`). `univCode` is a single fixed object (chosen once by
   `Classical.choose`); the dependence on `c` is moved entirely into the input `encode c`.
2. **Mathlib's machine chain.** `Turing.PartrecToTM2.tr` evaluates `univCode` on the stack machine
   model TM2 (`tr_eval`), supported on the finite set `codeSupp univCode Cont'.halt`
   (`tr_supports`, with that start label); `Turing.TM2to1` and `Turing.TM1to0` translate it to a
   one-tape machine `M₀ : TM0.Machine Γ₁ _` (`tr_eval_dom`, `tr_eval`, `tr_supports`), whose
   alphabet `Γ₁` is finite and whose reachable states lie in the finite set `S₀`.
3. **The list-encoded machine.** `compiler c = compile M₀ S₀ (input (encode c))`
   (`Compiler/TM0.lean`): the fixed table of `M₀` behind a prefix that writes Mathlib's initial tape
   for the input `[encode c]` (the TM2 input `trList [n]` multiplexed by `TM2to1.trInit`).
4. **Computability.** The table of `M₀` and its start state are constants; only the prefix depends
   on `c`, through the binary digits of `encode c` (`bin`, by iterated binary successor,
   primitive recursive) and three fixed symbol numbers (`input_map`).

**[choice]** The reduction is from Mathlib's halting problem at input `0`
(`ComputablePred.halting_problem 0`). The compiler is a Lean `noncomputable def`: the universal
code is chosen by `Classical.choose` from Mathlib's existence theorem, and the table of `M₀` is
listed through `Finset.toList` and `Fintype.equivFin`. This is harmless for the statement:
`Computable compiler` is Mathlib's property of the function (some `Nat.Partrec.Code` computes it),
proved here, and every classical choice enters only a constant.
-/
import FixedNoiseErgodicity.Compiler.TM0
import Mathlib.Computability.TuringMachine.ToPartrec
import Mathlib.Computability.PartrecBasis

set_option autoImplicit false

noncomputable section

namespace FNE.Compiler

open Turing

/-! ## Binary numerals -/

/-- Binary successor on little-endian lists of bits. -/
def bsucc : List Bool → List Bool
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: bsucc l

/-- The binary digits of `n` (least significant first): `n` successors of the empty list. -/
def bin (n : ℕ) : List Bool := bsucc^[n] []

/-- The digits of a positive binary numeral. -/
def pbits : PosNum → List Bool
  | .one => [true]
  | .bit0 p => false :: pbits p
  | .bit1 p => true :: pbits p

/-- The digits of a binary numeral. -/
def nbits : Num → List Bool
  | .zero => []
  | .pos p => pbits p

theorem pbits_succ (p : PosNum) : pbits p.succ = bsucc (pbits p) := by
  induction p with
  | one => rfl
  | bit1 p ih => simp only [PosNum.succ, pbits, bsucc, ih]
  | bit0 p => rfl

theorem nbits_succ (m : Num) : nbits m.succ = bsucc (nbits m) := by
  cases m with
  | zero => rfl
  | pos p => exact pbits_succ p

theorem bin_eq (n : ℕ) : bin n = nbits (n : Num) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hc : ((n + 1 : ℕ) : Num) = Num.succ (n : Num) := by
      rw [← Num.of_to_nat (Num.succ n), Num.succ_to_nat, Num.to_of_nat]
    rw [bin, Function.iterate_succ_apply', ← bin, ih, hc, nbits_succ]

/-- A bit as a binary digit of Mathlib's machine. -/
def bitSym (b : Bool) : PartrecToTM2.Γ' := cond b .bit1 .bit0

theorem trPosNum_eq (p : PosNum) : PartrecToTM2.trPosNum p = (pbits p).map bitSym := by
  induction p with
  | one => rfl
  | bit1 p ih => simp only [PartrecToTM2.trPosNum, pbits, ih, List.map_cons, bitSym, cond_true]
  | bit0 p ih => simp only [PartrecToTM2.trPosNum, pbits, ih, List.map_cons, bitSym, cond_false]

/-- Mathlib's binary encoding of `n` (`trNat`) is `bin n`, digit by digit. -/
theorem trNat_eq (n : ℕ) : PartrecToTM2.trNat n = (bin n).map bitSym := by
  rw [bin_eq, PartrecToTM2.trNat]
  generalize (n : Num) = m
  cases m with
  | zero => rfl
  | pos p => exact trPosNum_eq p

theorem bsucc_eq (l : List Bool) :
    bsucc l = List.recOn l [true] (fun b l IH => cond b (false :: IH) (true :: l)) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b
    · rfl
    · show false :: bsucc l = _
      rw [ih]
      rfl

theorem primrec_bsucc : Primrec bsucc := by
  have h : Primrec₂ fun (_ : List Bool) (p : Bool × List Bool × List Bool) =>
      cond p.1 (false :: p.2.2) (true :: p.2.1) :=
    (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.const false) (Primrec.snd.comp (Primrec.snd.comp
        Primrec.snd)))
      (Primrec.list_cons.comp (Primrec.const true) (Primrec.fst.comp (Primrec.snd.comp
        Primrec.snd)))).to₂
  exact (Primrec.list_rec Primrec.id (Primrec.const [true]) h).of_eq fun l => (bsucc_eq l).symm

theorem primrec_bin : Primrec bin :=
  (Primrec.nat_iterate Primrec.id (Primrec.const []) (primrec_bsucc.comp Primrec.snd).to₂).of_eq
    fun _ => rfl

/-! ## A universal code of Mathlib's `ToPartrec` model -/

/-- The universal partial function: `n ↦` the value at `0` of the code numbered `n`. -/
def univFun : ℕ →. ℕ := fun n => (Denumerable.ofNat Nat.Partrec.Code n).eval 0

theorem univFun_partrec : Partrec univFun :=
  Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const 0)

theorem exists_univCode :
    ∃ U : ToPartrec.Code, ∀ n : ℕ, U.eval [n] = pure <$> univFun n := by
  obtain ⟨U, hU⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.2 univFun_partrec)
  exact ⟨U, fun n => hU ⟨[n], rfl⟩⟩

/-- **The universal code** (one fixed code of Mathlib's `ToPartrec` model, chosen once). -/
def univCode : ToPartrec.Code := Classical.choose exists_univCode

theorem univCode_eval (n : ℕ) : univCode.eval [n] = pure <$> univFun n :=
  Classical.choose_spec exists_univCode n

/-! ## Mathlib's machine chain for the universal code -/

open PartrecToTM2

/-- The start label of Mathlib's TM2 machine `tr` on the universal code, as the `Inhabited`
instance (the form of Mathlib's `tr_supports`). -/
@[reducible] def startInst : Inhabited Λ' := ⟨trNormal univCode Cont'.halt⟩

attribute [local instance high] startInst

/-- The four stacks form a finite type (Mathlib derives only `DecidableEq` and `Inhabited`). -/
@[reducible] def fintypeK' : Fintype K' :=
  Fintype.ofList [K'.main, K'.rev, K'.aux, K'.stack] fun k => by cases k <;> simp

attribute [local instance] fintypeK'

/-- The tape alphabet of the one-tape simulations (`TM2to1.Γ'` for the four stacks). -/
abbrev Γ₁ := TM2to1.Γ' K' (fun _ => Γ')

/-- The labels of the TM1 simulation. -/
abbrev Λ₁ := TM2to1.Λ' K' (fun _ => Γ') Λ' (Option Γ')

/-- Mathlib's TM1 machine simulating `tr` (`TM2to1.tr`). -/
def M₁ : Λ₁ → TM1.Stmt Γ₁ Λ₁ (Option Γ') := TM2to1.tr tr

/-- Mathlib's TM0 machine simulating `M₁` (`TM1to0.tr`). -/
def M₀ : TM0.Machine Γ₁ (TM1to0.Λ' M₁) := TM1to0.tr M₁

/-- The finite set of reachable states of `M₀` (from Mathlib's supports). -/
def S₀ : Finset (TM1to0.Λ' M₁) :=
  TM1to0.trStmts M₁ (TM2to1.trSupp tr (codeSupp univCode Cont'.halt))

theorem supports₀ : TM0.Supports M₀ ↑S₀ :=
  TM1to0.tr_supports M₁ (TM2to1.tr_supports tr (tr_supports univCode Cont'.halt))

/-- The initial tape of `M₀` for the input `[n]`: Mathlib's `trList [n]` on the main stack. -/
def input (n : ℕ) : List Γ₁ := TM2to1.trInit K'.main (trList [n])

theorem input_ne_nil (n : ℕ) : input n ≠ [] := by
  simp [input, TM2to1.trInit]

theorem init_eq (v : List ℕ) :
    (TM2.init K'.main (trList v) : TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ')) =
      init univCode v := by
  simp only [TM2.init, init]
  congr 1
  funext k
  cases k <;> rfl

/-- `M₀` halts on `input n` iff the universal function is defined at `n`. -/
theorem eval_dom (n : ℕ) : (TM0.eval M₀ (input n)).Dom ↔ (univFun n).Dom := by
  rw [M₀, TM1to0.tr_eval, input, M₁]
  erw [TM2to1.tr_eval_dom]
  change (StateTransition.eval (TM2.step tr) (TM2.init K'.main (trList [n]))).Dom ↔ _
  rw [init_eq, tr_eval, univCode_eval]
  exact Iff.rfl

/-! ## The compiler -/

/-- **The compiler**: the code `c` becomes the list-encoded form of `M₀` on the input `[encode c]`. -/
def compiler (c : Nat.Partrec.Code) : TuringMachine :=
  compile M₀ S₀ (input (Encodable.encode c))

/-- **`compiler c` halts iff `c` halts on input `0`.** -/
theorem compiler_halts (c : Nat.Partrec.Code) : (compiler c).Halts ↔ (c.eval 0).Dom := by
  rw [compiler, compile_halts M₀ S₀ supports₀ (input_ne_nil _), eval_dom, univFun,
    Denumerable.ofNat_encode]

/-- The symbol under the head at the start: the bottom mark with `cons` on the main stack. -/
def topSym : Γ₁ := (true, Function.update (fun _ => none) K'.main (some Γ'.cons))

/-- A binary digit on the main stack. -/
def bitG (b : Bool) : Γ₁ := (false, Function.update (fun _ => none) K'.main (some (bitSym b)))

theorem input_eq (n : ℕ) : input n = topSym :: (bin n).reverse.map bitG := by
  simp only [input, TM2to1.trInit, trList, trNat_eq, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.map_cons,
    List.headI_cons, List.tail_cons, List.map_reverse, List.map_map]
  erw [List.map_cons, List.headI_cons, List.tail_cons, List.map_reverse, List.map_map]
  rfl

/-- The numbered input: a constant, then the binary digits of `n` (most significant first), each
digit one of two constants. -/
theorem input_map (n : ℕ) : (input n).map symNum =
    symNum topSym :: (bin n).reverse.map fun b => cond b (symNum (bitG true))
      (symNum (bitG false)) := by
  rw [input_eq, List.map_cons, List.map_map]
  congr 2
  funext b
  cases b <;> rfl

/-- **The compiler is primitive recursive.** -/
theorem primrec_compiler : Primrec compiler := by
  have h1 : Primrec fun n : ℕ => symNum topSym :: (bin n).reverse.map fun b =>
      cond b (symNum (bitG true)) (symNum (bitG false)) :=
    Primrec.list_cons.comp (Primrec.const _) (Primrec.list_map
      (Primrec.list_reverse.comp primrec_bin)
      (Primrec.cond Primrec.snd (Primrec.const _) (Primrec.const _)).to₂)
  refine ((primrec_mkMachine (stNum S₀ default) (table M₀ S₀)).comp
    (h1.comp Primrec.encode)).of_eq fun c => ?_
  rw [compiler, compile, input_map]

/-- **The compiler is computable.** -/
theorem computable_compiler : Computable compiler :=
  primrec_compiler.to_comp

end FNE.Compiler
