/-
# Challenge for the natural Wang rule on Z4 (Theorem 12.5).
Imports only Mathlib. Verbatim statement copies and UPD excerpts are generated from
the four vendored public cores and the frozen FLD statement file. The module-name,
auxiliary-proof-cache and matcher-cache handling is copied from the natural-rule
release generator. The three final holes have no hypotheses.
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Partrec
import Mathlib.Tactic.DeriveFintype
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Computability.Halting
import Mathlib.Data.Set.Countable
import Mathlib.Data.List.Nodup

/-! ## 1. The forgetting core's statement file -/

section

set_option bootstrap.genMatcherCode false

run_cmd Lean.modifyEnv (fun env => env.setMainModule `FixedNoiseErgodicity.Statements)
run_cmd Lean.modifyEnv (fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {})

-- BEGIN verbatim copy of FixedNoiseErgodicity/Statements.lean (the whole file except its import lines)
/-
Copyright (c) 2026 Seth Douglas, Nidhal Mghirbi. All rights reserved.
Formalization of: S. Douglas and N. Mghirbi, "Forgetting under noise is undecidable:
ergodicity of positive-rate cellular automata at a fixed noise rate", v1.3.0,
Zenodo DOI 10.5281/zenodo.24115709.

# Statement file

This file defines, transparently and with no proofs of substance, every object that occurs in
Corollary `cor:eight` of the paper (Theorem A on `ℤ⁸`, Section 9.6), and states that corollary as
the proposition `CorEight`; it is proved as `FNE.cor_eight : CorEight` in `Main.lean`. Every
definition carries a docstring citing the paper label it mirrors.
Fidelity choices are marked **[choice]** and are collected in `BLUEPRINT.md`, Part D.

Printed statement (cor:eight). Put `j = 3`, `k = max(2, 2j) = 6`, `q = k + 1 = 7`,
`a = 2q² + 1 = 99`, `D₀ = 50q = 350` and `ε₀ = (4D₀²)^(-a) = 490000^(-99)`. For every
`ε ∈ (0, ε₀]` and every Turing machine `M`, the noisy quorum rule `F^[6]_{R_M}` on `ℤ⁸`, with
uniform replacement at rate `ε`, is a positive-rate probabilistic cellular automaton, and it is
ergodic if and only if `M` halts. The map `M ↦ F^[6]_{R_M}` is total computable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace FNE

/-! ## Section 2.1: Wang sets, blocks and the checker -/

/-- `set:def-wang`. A Wang tile: its north, east, south and west edge colours.
**[choice]** Colours are natural numbers; any countable colour set can be relabelled so. -/
@[ext] structure Tile where
  /-- north edge colour -/
  N : ℕ
  /-- east edge colour -/
  E : ℕ
  /-- south edge colour -/
  S : ℕ
  /-- west edge colour -/
  W : ℕ
deriving DecidableEq

/-- `set:def-wang`. A Wang set is a finite set of tiles. -/
abbrev WangSet := Finset Tile

/-- The plane `ℤ²` of planar sites `u`. -/
abbrev Plane := ℤ × ℤ

/-- Section 2 (opening paragraph). The box `V_r = {-r, …, r}²`. -/
def box (r : ℕ) : Finset Plane :=
  Finset.Icc (-(r : ℤ)) r ×ˢ Finset.Icc (-(r : ℤ)) r

/-- Section 2. The cells of `Λ = V_1 = {-1, 0, 1}²`, as a finite type. -/
abbrev Cell := {w : Plane // w ∈ box 1}

/-- The centre `(0,0)` of `Λ`. -/
def Cell.zero : Cell := ⟨(0, 0), by decide⟩

/-- `set:def-live`. The Moore directions `D = Λ \ {(0,0)}`. -/
def mooreDirs : Finset Plane := (box 1).erase (0, 0)

/-- `set:def-wang`, `set:def-live`. A pattern `β : Λ → R` on the 3×3 window is *legal* if
horizontally adjacent cells match east-to-west and vertically adjacent cells match north-to-south.
(The pattern takes values in `R` by its type.) -/
def IsLegalBlock {R : WangSet} (β : Cell → R) : Prop :=
  (∀ w w' : Cell, w'.1 = w.1 + (1, 0) → (β w).1.E = (β w').1.W) ∧
  (∀ w w' : Cell, w'.1 = w.1 + (0, 1) → (β w).1.N = (β w').1.S)

instance {R : WangSet} : DecidablePred (IsLegalBlock (R := R)) := fun β => by
  unfold IsLegalBlock; infer_instance

/-- `set:def-live`. The set `T_R` of legal 3×3 blocks. -/
abbrev LegalBlock (R : WangSet) := {β : Cell → R // IsLegalBlock β}

/-- `set:def-live`. A live symbol `s = (λ, b)`: a legal block and a checker bit.
**[choice]** The checker bit `b ∈ {0,1}` is a `Bool` (`false` is `0`). -/
abbrev LiveSymbol (R : WangSet) := LegalBlock R × Bool

/-- `set:def-live`. The alphabet `𝒜_R = L_R ∪ {⊥}`. -/
inductive Sym (R : WangSet) where
  /-- the bottom symbol `⊥` -/
  | bot : Sym R
  /-- a live symbol -/
  | live : LiveSymbol R → Sym R
deriving DecidableEq

namespace Sym

variable {R : WangSet}

/-- `Sym R ≃ Option (LiveSymbol R)`, used only to transfer the finiteness instance. -/
def equivOption : Sym R ≃ Option (LiveSymbol R) where
  toFun | .bot => none | .live s => some s
  invFun | none => .bot | some s => .live s
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

instance : Fintype (Sym R) := Fintype.ofEquiv _ equivOption.symm

instance : Inhabited (Sym R) := ⟨.bot⟩

/-- The alphabet carries the discrete topology (Section 2.3: `Ω` has the product topology). -/
instance : TopologicalSpace (Sym R) := ⊥

instance : DiscreteTopology (Sym R) := ⟨rfl⟩

/-- The alphabet carries the discrete σ-algebra. -/
instance : MeasurableSpace (Sym R) := ⊤

instance : MeasurableSingletonClass (Sym R) := ⟨fun _ => trivial⟩

instance : BorelSpace (Sym R) := ⟨borel_eq_top_of_discrete.symm⟩

end Sym

/-- `set:def-live`. The live symbol `s'` is *compatible with `s` at displacement `d`*: the bits
agree, and `λ(w) = λ'(w - d)` for every `w ∈ Λ ∩ (d + Λ)`. -/
def Compatible {R : WangSet} (s s' : LiveSymbol R) (d : Plane) : Prop :=
  s.2 = s'.2 ∧ ∀ w w' : Cell, w'.1 = w.1 - d → s.1.1 w = s'.1.1 w'

/-- `set:def-live`. The centre `ctr(s) = λ(0,0)` of a live symbol. -/
def ctr {R : WangSet} (s : LiveSymbol R) : Tile := (s.1.1 Cell.zero).1

/-- `set:def-checker`. The condition under which the planar checker keeps `x(u)`: `x(u)` is
live and, for every `d ∈ D`, `x(u+d)` is live and compatible with `x(u)` at displacement `d`. -/
def CheckerKeeps {R : WangSet} (x : Plane → Sym R) (u : Plane) : Prop :=
  ∃ s, x u = .live s ∧ ∀ d ∈ mooreDirs, ∃ s', x (u + d) = .live s' ∧ Compatible s s' d

open Classical in
/-- `set:def-checker`. The planar checker `C : 𝒜_R^{ℤ²} → 𝒜_R^{ℤ²}`. -/
def checker {R : WangSet} (x : Plane → Sym R) : Plane → Sym R :=
  fun u => if CheckerKeeps x u then x u else .bot

/-! ## Section 2.2: the quorum rule and replacement noise -/

/-- `set:def-quorum`. Sites `(u, P) ∈ ℤ² × ℤᵏ`. For `k = 6` this is `ℤ⁸`.
**[choice]** `ℤ^{2+k}` is written `ℤ² × ℤᵏ`, as in the paper's coordinates `(u, P)`. -/
abbrev Site (k : ℕ) := Plane × (Fin k → ℤ)

/-- `set:def-quorum`. Configurations `Ω = 𝒜_R^{ℤ² × ℤᵏ}`. -/
abbrev Config (k : ℕ) (R : WangSet) := Site k → Sym R

/-- `set:def-quorum`. The providers `c_0 = 0` and `c_i = e_i` (`1 ≤ i ≤ k`).
**[choice]** The index set `{0, …, k}` is `Option (Fin k)`: `none` is `0` and `some i` is
`i + 1`. -/
def provider (k : ℕ) : Option (Fin k) → (Fin k → ℤ)
  | none => 0
  | some i => Pi.single i 1

/-- `set:def-quorum`. The checked configuration `y(u, P) = C(x(·, P))(u)`: the checker run in
every plane. -/
def checkAll {k : ℕ} {R : WangSet} (x : Config k R) : Config k R :=
  fun v => checker (fun u => x (u, v.2)) v.1

/-- `set:def-quorum`. The number `#{i ∈ {0,…,k} : y(u, P + c_i) = s}` of providers reading `s`. -/
def quorumCount {k : ℕ} {R : WangSet} (y : Config k R) (v : Site k) (s : Sym R) : ℕ :=
  (Finset.univ.filter (fun i : Option (Fin k) => y (v.1, v.2 + provider k i) = s)).card

open Classical in
/-- `set:def-quorum`. The quorum rule `F^[k]_R`: `F(x)(u,P) = s` if `s` is live and at least `k`
of the `k + 1` readings `y(u, P + c_i)` equal `s`; otherwise `⊥`.
**[choice]** The live symbol is picked with `Classical.choose`; for `k ≥ 2` it is unique
(`mem:basic`(a)), so the choice is immaterial for `k = 6`. -/
def quorumRule (k : ℕ) (R : WangSet) (x : Config k R) : Config k R := fun v =>
  if h : ∃ s : LiveSymbol R, k ≤ quorumCount (checkAll x) v (.live s) then .live h.choose
  else .bot

/-- `set:def-noise`. The law of a replacement indicator `η_t(v)`: `true` (a replacement event)
with probability `ε`. -/
def flagLaw (ε : ℝ) : Measure Bool :=
  ENNReal.ofReal ε • Measure.dirac true + ENNReal.ofReal (1 - ε) • Measure.dirac false

/-- `set:def-noise`. The uniform law on the alphabet `𝒜_R`, the law of a replacement value
`ζ_t(v)`. -/
def uniformSym (R : WangSet) : Measure (Sym R) :=
  (Fintype.card (Sym R) : ℝ≥0∞)⁻¹ • Measure.count

/-- `set:def-noise`. A noise realisation: `ω (t, v) = (η_{t+1}(v), ζ_{t+1}(v))` for `t ≥ 0`.
**[choice]** Time `t + 1 ≥ 1` of the paper is index `t` here. -/
abbrev Noise (k : ℕ) (R : WangSet) := ℕ × Site k → Bool × Sym R

/-- `set:def-noise`. The law of the noise: all `η_t(v)` and `ζ_t(v)` are independent,
`P(η_t(v) = 1) = ε` and `ζ_t(v)` is uniform on `𝒜_R`. -/
def noiseLaw (k : ℕ) (R : WangSet) (ε : ℝ) : Measure (Noise k R) :=
  Measure.infinitePi (fun _ : ℕ × Site k => (flagLaw ε).prod (uniformSym R))

/-- `set:def-noise`. The process from `x` driven by the noise `ω`: `X_0 = x` and
`X_{t+1}(v) = ζ_{t+1}(v)` if `η_{t+1}(v) = 1`, and `F^[k]_R(X_t)(v)` otherwise. -/
def run {k : ℕ} {R : WangSet} (x : Config k R) (ω : Noise k R) : ℕ → Config k R
  | 0 => x
  | t + 1 => fun v => if (ω (t, v)).1 then (ω (t, v)).2 else quorumRule k R (run x ω t) v

/-- `set:def-noise`. `μΦ^t`: the law of `X_t` when `X_0` has law `μ` and is independent of the
noise. -/
def law (k : ℕ) (R : WangSet) (ε : ℝ) (μ : Measure (Config k R)) (t : ℕ) :
    Measure (Config k R) :=
  (μ.prod (noiseLaw k R ε)).map (fun p => run p.1 p.2 t)

/-- `set:def-noise`. A measure `μ` is *invariant* if `μΦ = μ`. -/
def IsInvariant (k : ℕ) (R : WangSet) (ε : ℝ) (μ : Measure (Config k R)) : Prop :=
  law k R ε μ 1 = μ

/-- `set:def-noise` (the displayed formula after it). The law of `X_{t+1}(v)` given `X_t = x`:
`(1 - ε) δ_{F(x)(v)} + ε · uniform`. -/
def siteLaw (k : ℕ) (R : WangSet) (ε : ℝ) (x : Config k R) (v : Site k) : Measure (Sym R) :=
  ENNReal.ofReal (1 - ε) • Measure.dirac (quorumRule k R x v) + ENNReal.ofReal ε • uniformSym R

/-- `set:def-noise` and the paragraph after `set:def-quorum`: the process is a probabilistic
cellular automaton with positive rates. Spelled out:
(i) the deterministic rule commutes with every translation of `ℤ² × ℤᵏ`;
(ii) it is local, with neighbourhood `𝒩 = Λ × {c_0, …, c_k}`;
(iii) given `X_0 = x`, the values `X_1(v)` are independent with laws `siteLaw x v`;
(iv) every symbol has positive probability under every `siteLaw x v` ("positive rates").
**[choice]** The paper's phrase "positive-rate probabilistic cellular automaton" is rendered by
these four clauses. -/
def IsPositiveRatePCA (k : ℕ) (R : WangSet) (ε : ℝ) : Prop :=
  (∀ (w : Site k) (x : Config k R),
      quorumRule k R (fun v => x (v + w)) = fun v => quorumRule k R x (v + w)) ∧
  (∀ (x x' : Config k R) (v : Site k),
      (∀ d ∈ box 1, ∀ i : Option (Fin k),
        x (v + (d, provider k i)) = x' (v + (d, provider k i))) →
      quorumRule k R x v = quorumRule k R x' v) ∧
  (∀ x : Config k R,
      law k R ε (Measure.dirac x) 1 = Measure.infinitePi (fun v => siteLaw k R ε x v)) ∧
  (∀ (x : Config k R) (v : Site k) (s : Sym R), 0 < siteLaw k R ε x v {s})

/-! ## Section 2.3: ergodicity -/

/-- `set:def-ergodic` (weak convergence). `μ_t → π` weakly: `∫ f dμ_t → ∫ f dπ` for every bounded
continuous `f : Ω → ℝ`. `Ω` carries the product topology of the discrete alphabet. -/
def WeakTendsto {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    (μs : ℕ → Measure Ω) (π : Measure Ω) : Prop :=
  ∀ f : BoundedContinuousFunction Ω ℝ,
    Tendsto (fun t => ∫ x, f x ∂(μs t)) atTop (𝓝 (∫ x, f x ∂π))

/-- `set:def-ergodic`. The process is *ergodic* if it has exactly one invariant probability
measure `π`, and `μΦ^t → π` weakly for every probability measure `μ` on `Ω`. -/
def IsErgodic (k : ℕ) (R : WangSet) (ε : ℝ) : Prop :=
  ∃ π : Measure (Config k R), IsProbabilityMeasure π ∧ IsInvariant k R ε π ∧
    (∀ π' : Measure (Config k R), IsProbabilityMeasure π' → IsInvariant k R ε π' → π' = π) ∧
    ∀ μ : Measure (Config k R), IsProbabilityMeasure μ → WeakTendsto (fun t => law k R ε μ t) π

/-! ## Turing machines (Section 6.6, paragraph "Machines") -/

/-- Head moves. -/
inductive Move where
  | left
  | stay
  | right
deriving DecidableEq

/-- The displacement of a head move. -/
def Move.toInt : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

/-- Section 6.6, "Machines": a Turing machine has finitely many states, among them an initial
state and a set of halting states, a finite tape alphabet with a blank symbol, and a transition
function; it runs on a two-sided tape.
**[choice]** Finite encoding: states and tape symbols are natural numbers, the initial state is
`0` and the blank is `0`. The transition function is `table`: on state `q` reading `a`, the
first entry `((q, a), (q', a', m))` says: go to `q'`, write `a'`, move by `m`. A pair `(q, a)` with
no entry leaves the configuration unchanged (an idle self-loop). The states of the machine are
`0` and the states occurring in `table` and `halting`; its symbols are `0` and the symbols
occurring in `table`. Every machine of the paper has such an encoding. -/
structure TuringMachine where
  /-- transition table -/
  table : List ((ℕ × ℕ) × (ℕ × ℕ × Move))
  /-- halting states -/
  halting : List ℕ

/-- A configuration of a Turing machine: state, head position, two-sided tape. -/
structure TMConfig where
  /-- current state -/
  state : ℕ
  /-- head position -/
  head : ℤ
  /-- tape contents -/
  tape : ℤ → ℕ

namespace TuringMachine

/-- The start: initial state `0`, head at `0`, blank (all-`0`) two-sided tape. -/
def start : TMConfig := ⟨0, 0, fun _ => 0⟩

/-- One step of the machine. -/
def step (M : TuringMachine) (c : TMConfig) : TMConfig :=
  match M.table.lookup (c.state, c.tape c.head) with
  | some (q, a, m) => ⟨q, c.head + m.toInt, Function.update c.tape c.head a⟩
  | none => c

/-- Section 6.6: `M` *halts* if, started on a blank two-sided tape, it enters a halting state. -/
def Halts (M : TuringMachine) : Prop :=
  ∃ n : ℕ, (M.step^[n] start).state ∈ M.halting

end TuringMachine

/-! ## Encodings for computability -/

/-- `Move ≃ Fin 3`. -/
def Move.equivFin : Move ≃ Fin 3 where
  toFun | .left => 0 | .stay => 1 | .right => 2
  invFun i := if i = 0 then .left else if i = 1 then .stay else .right
  left_inv m := by cases m <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Primcodable Move := Primcodable.ofEquiv _ Move.equivFin

/-- `TuringMachine ≃ (table, halting states)`. -/
def TuringMachine.equivProd :
    TuringMachine ≃ List ((ℕ × ℕ) × (ℕ × ℕ × Move)) × List ℕ where
  toFun M := (M.table, M.halting)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable TuringMachine := Primcodable.ofEquiv _ TuringMachine.equivProd

/-- `Tile ≃ ℕ⁴`. -/
def Tile.equivProd : Tile ≃ ℕ × ℕ × ℕ × ℕ where
  toFun t := (t.N, t.E, t.S, t.W)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable Tile := Primcodable.ofEquiv _ Tile.equivProd

/-! ## Corollary `cor:eight` -/

/-- `cor:eight`. The rate `ε₀ = (4 D₀²)^(-a)` with `q = 7`, `D₀ = 50 q = 350` and
`a = 2 q² + 1 = 99`; numerically `490000^(-99)` (see `eps0_eq` in `Basic.lean`). -/
def eps0 : ℝ := ((4 * (50 * 7 : ℝ) ^ 2) ^ (2 * 7 ^ 2 + 1))⁻¹

/-- **Corollary `cor:eight` (Theorem A on `ℤ⁸`).** There is a total computable map `M ↦ R_M`
from Turing machines to finite Wang sets such that for every `ε ∈ (0, ε₀]` and every machine
`M`, the noisy quorum rule `F^[6]_{R_M}` on `ℤ² × ℤ⁶ = ℤ⁸` with uniform replacement at rate `ε`
is a positive-rate probabilistic cellular automaton, and it is ergodic if and only if `M` halts.

**[choice]** The family is quantified existentially (the paper's family `R_M` of `def:family`
is the intended witness; see `BLUEPRINT.md`, decision D2). A Wang set is computed as a list
of tiles (`Finset` has no `Primcodable` instance in Mathlib); the Wang set is its set of
entries. Computability of `M ↦ F^[6]_{R_M}` is rendered as computability of `M ↦ R_M`, from
which the local rule is an explicit finite construction (decision D4). -/
def CorEight : Prop :=
    ∃ Rfam : TuringMachine → List Tile, Computable Rfam ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ eps0 → ∀ M : TuringMachine,
        IsPositiveRatePCA 6 (Rfam M).toFinset ε ∧
          (IsErgodic 6 (Rfam M).toFinset ε ↔ M.Halts)

end FNE
-- END verbatim copy of FixedNoiseErgodicity/Statements.lean
end

end

/-! ## 2. From the hard-model core: `UPD.Machine`, `UPD.Machine.HaltsOn`, `UPD.Universal` -/

section

set_option backward.isDefEq.respectTransparency false
set_option bootstrap.genMatcherCode false

run_cmd Lean.modifyEnv (fun env => env.setMainModule `UndecidablePhaseDiagram.Statements)
run_cmd Lean.modifyEnv (fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {})

-- BEGIN verbatim excerpt of UndecidablePhaseDiagram/Statements.lean, lines 41-53 (header: options, section, opens, namespace)
set_option autoImplicit false

-- The `deriving Fintype` handler builds the instance through nested sigma types; the records of
-- Section 4 have up to 21 fields, which exceeds the default instance-size budget.
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UPD
-- END verbatim excerpt of UndecidablePhaseDiagram/Statements.lean, lines 41-53

-- BEGIN verbatim excerpt of UndecidablePhaseDiagram/Statements.lean, lines 143-206 (Section 2.2: UPD.Machine, State, Symbol, Cfg, step, start, run, HaltsOn)
/-! ## Section 2.2: Turing machines -/

/-- Section 2.2. A deterministic Turing machine with a one-sided tape (cells `0, 1, 2, …`).
**[choice]** Finite encoding: the states are `Fin (numStates + 1)` with initial state `0`; the
tape symbols are `Fin (numSymbols + 2)`, with blank `0` and the symbol `1`; the halting states are
those with `halting q = true`; `trans q γ = (q', γ', D)`: write `γ'`, go to `q'`, move one cell
right if `D = true` and one cell left if `D = false`. The initial state is not halting (the paper's
machine `M` enters the state `(q⁰_U, run)`, which exists only for a non-halting `q⁰_U`).
Every machine of Section 2.2 with a non-halting initial state has such an encoding. -/
structure Machine where
  /-- the states are `Fin (numStates + 1)` -/
  numStates : ℕ
  /-- the tape symbols are `Fin (numSymbols + 2)` -/
  numSymbols : ℕ
  /-- the halting states -/
  halting : Fin (numStates + 1) → Bool
  /-- the transition function -/
  trans : Fin (numStates + 1) → Fin (numSymbols + 2) →
    Fin (numStates + 1) × Fin (numSymbols + 2) × Bool
  /-- the initial state `0` is not halting -/
  init_not_halting : halting 0 = false

namespace Machine

/-- The states of a machine. -/
abbrev State (U : Machine) := Fin (U.numStates + 1)

/-- The tape symbols of a machine; `0` is the blank `⊔` and `1` is the symbol `1`. -/
abbrev Symbol (U : Machine) := Fin (U.numSymbols + 2)

/-- A configuration: state, head cell, one-sided tape. -/
structure Cfg (U : Machine) where
  /-- the state -/
  state : U.State
  /-- the head cell -/
  head : ℕ
  /-- the tape -/
  tape : ℕ → U.Symbol

/-- Section 2.2. One step: write, change state, move one cell left or right.
**[choice]** A move left from cell `0` ends the run without halting (`none`); the paper's
convention is that the machine never makes such a move, and then this case never occurs. -/
def step (U : Machine) (c : U.Cfg) : Option U.Cfg :=
  let t := U.trans c.state (c.tape c.head)
  if t.2.2 then some ⟨t.1, c.head + 1, Function.update c.tape c.head t.2.1⟩
  else if c.head = 0 then none
  else some ⟨t.1, c.head - 1, Function.update c.tape c.head t.2.1⟩

/-- Section 2.2. The start on input `n`: initial state, head on cell `0`, cells `0, …, n-1` hold
the symbol `1`, all other cells are blank. -/
def start (U : Machine) (n : ℕ) : U.Cfg :=
  ⟨0, 0, fun j => if j < n then 1 else 0⟩

/-- The configuration after `t` steps on input `n` (`none` once the run has ended by a move left
from cell `0`). -/
def run (U : Machine) (n : ℕ) : ℕ → Option U.Cfg
  | 0 => some (U.start n)
  | t + 1 => (U.run n t).bind U.step

/-- Section 2.2. `U` halts on input `n` if, started on input `n`, it enters a halting state. -/
def HaltsOn (U : Machine) (n : ℕ) : Prop :=
  ∃ (t : ℕ) (c : U.Cfg), U.run n t = some c ∧ U.halting c.state = true

end Machine
-- END verbatim excerpt of UndecidablePhaseDiagram/Statements.lean, lines 143-206

-- BEGIN verbatim excerpt of UndecidablePhaseDiagram/Statements.lean, lines 1232-1236 (UPD.Universal)
/-- Section 2.2: `U` is universal: its halting set `ℋ_U = {n ≥ 1 : U halts on n}` is not
decidable. **[choice]** The paper fixes `U` with `ℋ_U` `Σ⁰₁`-complete, "in particular
undecidable"; only undecidability is used, so it is the hypothesis here (a weaker hypothesis, a
stronger corollary). That such machines exist is `ExistsUniversal`. -/
def Universal (U : Machine) : Prop := ¬ ComputablePred (fun n : ℕ => 1 ≤ n ∧ U.HaltsOn n)
-- END verbatim excerpt of UndecidablePhaseDiagram/Statements.lean, lines 1232-1236

end UPD

end

end

/-! ## 3. The noise-diagram core's statement file -/

run_cmd Lean.modifyEnv (fun env => env.setMainModule `UncomputableNoiseDiagram.Statements)
run_cmd Lean.modifyEnv (fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {})

-- BEGIN verbatim copy of UncomputableNoiseDiagram/Statements.lean (the whole file except its import lines)
/-
Copyright (c) 2026 Seth Douglas, Nidhal Mghirbi. All rights reserved.
Released under the Apache License 2.0.
Formalization of: S. Douglas and N. Mghirbi, "One noisy cellular automaton with an uncomputable
noise diagram", v1.0.0, Zenodo DOI 10.5281/zenodo.24147269.

# Statement file

This file defines, transparently and with no proofs of substance, every object that occurs in
Theorem 9.3 (`thm:main`, printed in Section 9; Theorem A of the introduction) and Corollary 9.4
(`cor:undecidable`), and states them as the propositions `UND.TheoremA` and
`UND.CorollaryNineFour`. Following the ruling made for the forgetting core (session 9) and used
by the hard-model core, the statement file holds the propositions; the theorems
`UND.theorem_A : UND.TheoremA` and `UND.corollary_9_4 : UND.CorollaryNineFour` live in
`Main.lean`. Every definition carries a docstring citing the paper passage it mirrors.
Fidelity choices are marked **[choice]**; each is explained in `STATUS.md` ("Statement fidelity")
and `BLUEPRINT.md`, Part D.

Reused statement-level definitions (exact matches, imported, not copied):
* from the forgetting core (`FixedNoiseErgodicity/Statements.lean`): `FNE.flagLaw` (the law of a
  replacement flag) and `FNE.WeakTendsto` (weak convergence of laws);
* from the hard-model core (`UndecidablePhaseDiagram/Statements.lean`): `UPD.Machine` (a
  deterministic one-way-tape machine on unary inputs), `UPD.Machine.HaltsOn`, `UPD.Universal`
  (undecidable halting set on positive inputs) and `UPD.ExistsUniversal`.
The forgetting core's process, law, invariance and ergodicity (`FNE.run`, `FNE.law`,
`FNE.IsInvariant`, `FNE.IsErgodic`) are hard-wired to its quorum rule `F^[k]_R` on `ℤ² × ℤᵏ`, so
they are re-defined here, in the same shape, for an arbitrary cellular automaton.

Printed statement (Theorem A). Fix a universal deterministic machine `U` whose halting set on
positive unary inputs is undecidable. There is one computably specified cellular automaton on
`ℤ⁶`, with a finite alphabet and a finite neighbourhood, and computable disjoint rational open
intervals `I_n`, such that at every rate in `I_n` uniform whole-symbol replacement makes the
automaton ergodic exactly when `U(n)` halts. Nonhalting gives at least two
translation-invariant stationary laws. Halting gives a unique stationary law attracting every
initial law.

Printed statement (Theorem 9.3). For the single automaton (6) and the rational intervals (17),
for every `n ≥ 1` and every `ε ∈ I_n`, `F_ε` is ergodic iff `U(n)` halts. If `U(n)` does
not halt there are at least two translation-invariant stationary laws. If it halts the unique
stationary law attracts every initial law, and every finite-window common-noise pullback image is
almost surely eventually a singleton.

Printed statement (Corollary 9.4). For this fixed automaton, deciding ergodicity at a rational
noise rate is undecidable, even under the promise that the rate lies in one of the intervals
`I_n`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UND

/-! ## Section 2: cellular automata and uniform replacement -/

/-- Section 2, first paragraph: the lattice `ℤ^d`; a site is a map `Fin d → ℤ`.
**[choice]** `ℤ⁶` is `Fin 6 → ℤ`; the paper's coordinates `(u, P) ∈ ℤ² × ℤ⁴` are an
identification made inside the proof. -/
abbrev Site (d : ℕ) := Fin d → ℤ

/-- Section 2, first paragraph: "A cellular automaton on a finite alphabet `Σ` and lattice `ℤ^d`
is a map `F` given by one finite neighbourhood `N_F` and one function `f : Σ^{N_F} → Σ`."
**[choice]** The finite alphabet is `Fin numSymbols` with `numSymbols > 0` (every finite alphabet
is in bijection with such a type; nonemptiness makes the uniform law a probability measure). The
neighbourhood is a finite set of displacements; the local function reads the configuration on
`w + N_F`. -/
structure CA (d : ℕ) where
  /-- the size `|Σ|` of the alphabet; the symbols are `Fin numSymbols` -/
  numSymbols : ℕ
  /-- the alphabet is nonempty -/
  numSymbols_pos : 0 < numSymbols
  /-- the finite neighbourhood `N_F` -/
  nbhd : Finset (Site d)
  /-- the local function `f : Σ^{N_F} → Σ` -/
  localRule : (nbhd → Fin numSymbols) → Fin numSymbols

namespace CA

variable {d : ℕ}

/-- The alphabet `Σ` of a cellular automaton. It carries the discrete topology and the discrete
σ-algebra (Mathlib's instances on `Fin n`). -/
abbrev Sym (A : CA d) := Fin A.numSymbols

/-- Configurations `Σ^{ℤ^d}`, with the product topology and the product σ-algebra. -/
abbrev Config (A : CA d) := Site d → A.Sym

/-- Section 2: the global map `F(x)(w) = f((x(w + z))_{z ∈ N_F})`. It commutes with every
translation by construction. -/
def apply (A : CA d) (x : A.Config) : A.Config :=
  fun w => A.localRule (fun z => x (w + z.1))

/-- Section 2: the uniform law on `Σ`, the law of a replacement value `Z_t(w)`. -/
def uniformLaw (A : CA d) : Measure A.Sym :=
  (A.numSymbols : ℝ≥0∞)⁻¹ • Measure.count

/-- Section 2: a one-sided noise realisation, `ω (t, w) = (E_{t+1}(w), Z_{t+1}(w))` for `t ≥ 0`.
**[choice]** As in the forgetting core, the process starts at time `0`; the paper's time
`t + 1 ≥ 1` is index `t` here. -/
abbrev Noise (A : CA d) := ℕ × Site d → Bool × A.Sym

/-- Section 2: "independent variables `E_t(w) ∼ Bernoulli(ε)` and `Z_t(w)` uniform on `Σ`, at all
sites and integer times". The flag law is the forgetting core's `FNE.flagLaw`. -/
def noiseLaw (A : CA d) (ε : ℝ) : Measure A.Noise :=
  Measure.infinitePi (fun _ : ℕ × Site d => (FNE.flagLaw ε).prod A.uniformLaw)

/-- Section 2, the displayed update: `X_t(w) = Z_t(w)` if `E_t(w) = 1` and `F(X_{t-1})(w)` if
`E_t(w) = 0`, for one time slice `e = (E_t, Z_t)` of the noise. "The replacement is of the entire
product symbol." -/
def update (A : CA d) (e : Site d → Bool × A.Sym) (x : A.Config) : A.Config :=
  fun w => if (e w).1 then (e w).2 else A.apply x w

/-- Section 2: the process from `X_0 = x` driven by the noise `ω`. -/
def run (A : CA d) (x : A.Config) (ω : A.Noise) : ℕ → A.Config
  | 0 => x
  | t + 1 => A.update (fun w => ω (t, w)) (A.run x ω t)

/-- Section 2: `μ F_ε^t`, the law of `X_t` when `X_0` has law `μ` and is independent of the noise. -/
def law (A : CA d) (ε : ℝ) (μ : Measure A.Config) (t : ℕ) : Measure A.Config :=
  (μ.prod (A.noiseLaw ε)).map (fun p => A.run p.1 p.2 t)

/-- Section 2: "A stationary law is fixed by this Markov kernel": `μ F_ε = μ`. (The forgetting
core's `FNE.IsInvariant`, for this automaton.) -/
def IsStationary (A : CA d) (ε : ℝ) (μ : Measure A.Config) : Prop :=
  A.law ε μ 1 = μ

/-- Section 2: "Ergodicity means a unique stationary law and weak convergence to it from every
initial law." Same shape as the forgetting core's `FNE.IsErgodic`; weak convergence is
`FNE.WeakTendsto` (convergence of integrals of bounded continuous functions). -/
def IsErgodic (A : CA d) (ε : ℝ) : Prop :=
  ∃ π : Measure A.Config, IsProbabilityMeasure π ∧ A.IsStationary ε π ∧
    (∀ π' : Measure A.Config, IsProbabilityMeasure π' → A.IsStationary ε π' → π' = π) ∧
    ∀ μ : Measure A.Config, IsProbabilityMeasure μ →
      FNE.WeakTendsto (fun t => A.law ε μ t) π

/-- The spatial translate `(T_a x)(w) = x(w + a)`. -/
def shift (A : CA d) (a : Site d) (x : A.Config) : A.Config := fun w => x (w + a)

/-- Section 2: "Translation invariance means invariance under every spatial translation." -/
def IsTranslationInvariant (A : CA d) (μ : Measure A.Config) : Prop :=
  ∀ a : Site d, μ.map (A.shift a) = μ

/-- Theorem 9.3: at least two (distinct) translation-invariant stationary laws. -/
def HasTwoTIStationaryLaws (A : CA d) (ε : ℝ) : Prop :=
  ∃ μ₁ μ₂ : Measure A.Config, μ₁ ≠ μ₂ ∧
    IsProbabilityMeasure μ₁ ∧ A.IsStationary ε μ₁ ∧ A.IsTranslationInvariant μ₁ ∧
    IsProbabilityMeasure μ₂ ∧ A.IsStationary ε μ₂ ∧ A.IsTranslationInvariant μ₂

/-! ## Common-noise pullbacks (Lemma 8.5, `lem:pullback`; last clause of Theorem 9.3) -/

/-- Lemma 8.5: a two-sided noise realisation, `ω (t, w) = (E_t(w), Z_t(w))` at every integer time
`t` and site `w`. -/
abbrev Noise₂ (A : CA d) := ℤ × Site d → Bool × A.Sym

/-- The law of the two-sided noise: all flags and values independent, as in `noiseLaw`. -/
def noiseLaw₂ (A : CA d) (ε : ℝ) : Measure A.Noise₂ :=
  Measure.infinitePi (fun _ : ℤ × Site d => (FNE.flagLaw ε).prod A.uniformLaw)

/-- Lemma 8.5: `flow ω s n x` is the state at time `s + n` of the trajectory started from `x` at
time `s`, driven by the common noise `ω` (the map `Ψ_{s, s+n}`). -/
def flow (A : CA d) (ω : A.Noise₂) (s : ℤ) : ℕ → A.Config → A.Config
  | 0, x => x
  | n + 1, x => A.update (fun w => ω (s + n + 1, w)) (A.flow ω s n x)

/-- Lemma 8.5: the pullback `Ψ_{-j,0}(x)`: start from `x` at time `-j`, read at time `0`. -/
def pullback (A : CA d) (ω : A.Noise₂) (j : ℕ) (x : A.Config) : A.Config :=
  A.flow ω (-(j : ℤ)) j x

/-- Theorem 9.3, last clause: "every finite-window common-noise pullback image is almost surely
eventually a singleton". For every finite window `O`, almost surely there is `j₀` such that for
`j ≥ j₀` the projection to `O` of `K_j = Ψ_{-j,0}(Σ^{ℤ^d})` is one point. -/
def PullbackEventuallySingleton (A : CA d) (ε : ℝ) : Prop :=
  ∀ O : Finset (Site d), ∀ᵐ ω ∂(A.noiseLaw₂ ε), ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
    ∀ x x' : A.Config, ∀ w ∈ O, A.pullback ω j x w = A.pullback ω j x' w

end CA

/-! ## The intervals (Section 6, displayed windows; Theorem 9.3) -/

/-- A positive rational `p.1 / p.2` presented by a pair of natural numbers with `p.2 > 0`.
**[choice]** As in the hard-model core (`UPD.CorollaryB`): rational endpoints "computable from
`n`" means that some computable map `n ↦ (p, q)` presents them. -/
def Presents (p : ℕ × ℕ) (r : ℚ) : Prop := 0 < p.2 ∧ ((p.1 : ℚ) / p.2) = r

/-- The open interval `I_n = (lo n, hi n)` of real rates. -/
def window (lo hi : ℕ → ℚ) (n : ℕ) : Set ℝ := Set.Ioo (lo n : ℝ) (hi n : ℝ)

/-- Theorem A: "computable disjoint rational open intervals `I_n`" (`n ≥ 1`). The endpoints have
computable presentations; every interval is a nonempty open interval of rates in `(0, 1)`; the
intervals are pairwise disjoint.
**[choice]** "Rates" is made explicit as `0 < lo n` and `hi n < 1` (true of the paper's
intervals, which lie below `ε_*`, and needed for `F_ε` to be a noise rate). -/
def IsWindowFamily (lo hi : ℕ → ℚ) : Prop :=
  (∃ f : ℕ → ℕ × ℕ, Computable f ∧ ∀ n, Presents (f n) (lo n)) ∧
  (∃ g : ℕ → ℕ × ℕ, Computable g ∧ ∀ n, Presents (g n) (hi n)) ∧
  (∀ n : ℕ, 1 ≤ n → 0 < lo n ∧ lo n < hi n ∧ hi n < 1) ∧
  (∀ n m : ℕ, 1 ≤ n → 1 ≤ m → n ≠ m → Disjoint (window lo hi n) (window lo hi m))

/-! ## Theorem 9.3 (Theorem A) and Corollary 9.4 -/

/-- The clauses of Theorem 9.3 for a machine `U`, an automaton `A` on `ℤ⁶` and intervals
`I_n = (lo n, hi n)`: the intervals are as in `IsWindowFamily`, and for every `n ≥ 1` and every
`ε ∈ I_n`: `F_ε` is ergodic iff `U(n)` halts; if `U(n)` does not halt there are at least two
translation-invariant stationary laws; if it halts, `F_ε` has a unique stationary law attracting
every initial law (ergodicity) and every finite-window pullback image is almost surely eventually
a singleton. -/
def NoiseDiagram (U : UPD.Machine) (A : CA 6) (lo hi : ℕ → ℚ) : Prop :=
  IsWindowFamily lo hi ∧
  ∀ n : ℕ, 1 ≤ n → ∀ ε ∈ window lo hi n,
    (A.IsErgodic ε ↔ U.HaltsOn n) ∧
    (¬ U.HaltsOn n → A.HasTwoTIStationaryLaws ε) ∧
    (U.HaltsOn n → A.IsErgodic ε ∧ A.PullbackEventuallySingleton ε)

/-- **Theorem A / Theorem 9.3.** For the machine `U` there are one cellular automaton on `ℤ⁶` with
a finite alphabet and a finite neighbourhood, and computable pairwise disjoint rational open
intervals `I_n`, with the clauses of `NoiseDiagram`.
**[choice]** Stated for every machine `U` (the construction does not use universality; as in
`UPD.TheoremA`). "Computably specified" has no formal content for one finite object and is not
rendered: the development gives the automaton by explicit definitions (see `STATUS.md`,
"Statement fidelity", item F9). -/
def TheoremA : Prop :=
  ∀ U : UPD.Machine, ∃ (A : CA 6) (lo hi : ℕ → ℚ), NoiseDiagram U A lo hi

/-- Corollary 9.4: no algorithm decides ergodicity at the rational rates of the intervals.
**[choice]** A rate is presented by a pair `p` of natural numbers (`p.1 / p.2`, `p.2 > 0`, as in
`Presents`); the promise problem is undecidable: no computable `g` answers correctly on every
presentation of a rate in some `I_n`, `n ≥ 1`. -/
def PromiseUndecidable (A : CA 6) (lo hi : ℕ → ℚ) : Prop :=
  ¬ ∃ g : ℕ × ℕ → Bool, Computable g ∧
    ∀ n : ℕ, 1 ≤ n → ∀ p : ℕ × ℕ, 0 < p.2 → ((p.1 : ℝ) / p.2) ∈ window lo hi n →
      (g p = true ↔ A.IsErgodic ((p.1 : ℝ) / p.2))

/-- **Corollary 9.4.** For a universal machine `U` (halting set on positive inputs undecidable),
the automaton and intervals of Theorem 9.3 can be chosen so that, for this fixed automaton,
ergodicity at rational rates is undecidable even under the promise that the rate lies in one of
the `I_n`. ("This fixed automaton" is rendered by stating both conclusions for the same `A`.) -/
def CorollaryNineFour : Prop :=
  ∀ U : UPD.Machine, UPD.Universal U →
    ∃ (A : CA 6) (lo hi : ℕ → ℚ), NoiseDiagram U A lo hi ∧ PromiseUndecidable A lo hi

/-- The sentence after Theorem A ("the noise diagram ... is undecidable at rational rates for this
rule") with a universal machine supplied: one fixed automaton on `ℤ⁶` whose ergodicity at the
rational rates of computable disjoint windows is undecidable. Follows from `CorollaryNineFour`
and `UPD.ExistsUniversal`. -/
def OneRuleUndecidable : Prop :=
  ∃ (A : CA 6) (lo hi : ℕ → ℚ), IsWindowFamily lo hi ∧ PromiseUndecidable A lo hi

end UND
-- END verbatim copy of UncomputableNoiseDiagram/Statements.lean
end

/-! ## 4. The public natural-rule statement file -/

run_cmd Lean.modifyEnv (fun env => env.setMainModule `ForgettingNaturalRule.Statements)
run_cmd Lean.modifyEnv (fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {})

-- BEGIN verbatim copy of ForgettingNaturalRule/Statements.lean (the whole file except its import lines)
/-
Copyright (c) 2026 Seth Douglas, Nidhal Mghirbi. All rights reserved.
Released under the Apache License 2.0.
Formalization of: S. Douglas and N. Mghirbi, "Forgetting under noise is undecidable", version
2.0.0 (draft of 12 Nov 2026): Theorem D and Theorem A of the introduction (environments `mainD`,
`mainA`), with Section 2 (`sec:natural`, Theorem `nw:classification`) and Section 3
(Corollary `nw:machine`).

# Statement file — FROZEN (session 3, 12 Nov 2026)

Frozen after a blind fidelity read against the paper (`STATEMENT-READ.md`). The read found one
mismatch, which is fixed here: Theorem A is stated as printed, with no hypothesis (`FNR.TheoremA`).
Its note on translation invariance is applied in the docstring of `FNR.NaturalClassification`.
Its sha256 is recorded in `STATUS.md` as the statement of record; this file does not change again.

This file defines, transparently and with no proofs of substance, every object that occurs in the
two printed statements, and states them as the propositions `FNR.NaturalClassification`
(Theorem D) and `FNR.TheoremA` (Theorem A on `ℤ⁶`). As in the three earlier cores, the statement
file holds the propositions; the theorems live in the proof files: `FNR.natural_classification`
in `Main.lean`, and `FNR.theorem_A` in `Reduction.lean`. Every definition carries a docstring
citing the paper passage it mirrors. Fidelity choices are marked **[choice]** and are collected in
`STATUS.md` ("Statement fidelity").

Reused statement-level definitions (exact matches, imported, not copied):
* from the forgetting core (`FixedNoiseErgodicity/Statements.lean`): `FNE.Tile` (a Wang tile with
  natural-number edge colours `N, E, S, W`, with its `Primcodable` instance), `FNE.WangSet`
  (a finite set of tiles), `FNE.Plane` (`ℤ²`), the Turing machines `FNE.TuringMachine` (with their
  `Primcodable` instance) and halting from the blank tape `FNE.TuringMachine.Halts` (the machine
  model of the forgetting core's `FNE.CorEight`), and, through the next item, `FNE.flagLaw` and
  `FNE.WeakTendsto`;
* from the noise-diagram core (`UncomputableNoiseDiagram/Statements.lean`): `UND.Site`, the
  cellular automata `UND.CA` on `ℤ^d` (alphabet `Fin n`, finite neighbourhood, local rule, global
  map `UND.CA.apply`), uniform whole-symbol replacement `UND.CA.uniformLaw`, `UND.CA.noiseLaw`,
  the process `UND.CA.run`, its law `UND.CA.law`, stationarity `UND.CA.IsStationary`, ergodicity
  `UND.CA.IsErgodic` (a unique stationary probability law, and weak convergence to it from every
  initial probability law), the translates `UND.CA.shift`, translation invariance
  `UND.CA.IsTranslationInvariant` (invariance under every translation of `ℤ^d`) and
  `UND.CA.HasTwoTIStationaryLaws` (two distinct translation-invariant stationary probability laws).

Printed statement (Theorem D, introduction; Theorem `nw:classification`). Put `K = 16⁴`, `q = 5K`,
`h = 4K` and `ε_* = (2(18q)²)^(-200)`. For every finite Wang set `R`, a cardinal checker followed
by an `h`-of-`q` quorum in five fixed transverse boxes defines a rule `G_R` on `ℤ⁶` with alphabet
`R ⊔ {⊥}`. At every `0 < ε ≤ ε_*`, uniform whole-symbol replacement after `G_R` is ergodic if and
only if `R` does not tile the plane. If `R` tiles, there are two distinct translation-invariant
stationary laws.

Printed statement (Theorem A, introduction; Corollary `nw:machine`). There is a total computable
map `M ↦ W_M` from Turing machines to finite Wang sets such that, for every `ε ∈ (0, ε_*]`, the
positive-rate automaton obtained from `G_{W_M}` is ergodic if and only if `M` halts.
The printed statement has no hypothesis, and neither has `FNR.TheoremA`.

Also stated:
* `FNR.DominoReduction`: the classical domino reduction of Berger (1966) and Robinson (1971), the
  first sentence of `nw:machine` (paper: "The only undecidability input in this route is the
  classical domino reduction of Berger and Robinson");
* `FNR.TheoremAFromDomino`: Theorem A from that reduction (`DominoReduction → ErgodicityReduction`),
  the route of the paper's proof; a conditional form, weaker than `FNR.TheoremA`, not a printed
  statement;
* `FNR.MachineCorollary`: Corollary `nw:machine` in full (the reduction, the ergodicity clause for
  the same map, and "In particular ergodicity is undecidable at each one of these fixed rates");
* the undecidability form of session 1, `FNR.TheoremAUndecidable` (a corollary, not a printed
  environment; with Berger's theorem "the domino problem is undecidable", `FNR.DominoUndecidable`,
  as its hypothesis), the last sentence of `nw:machine` for the raw inputs `R`.

Not stated here (outside the core, by QB's ruling): the coalescence bound (`nw:coalescence`) of
Theorem `nw:classification`, nilpotency, and the other consequences of Section 3 of the paper.
-/

set_option autoImplicit false

noncomputable section

namespace FNR

open FNE (Tile WangSet Plane TuringMachine)

/-! ## Tilings (Section 2.2, "Tiles, configurations and noise") -/

/-- Section 2.2: "A finite Wang set `R` tiles the plane if there is `θ : ℤ² → R` whose shared
horizontal and vertical edge colours match. Translations are allowed, rotations and reflections
are not." The tile `θ (u + (1, 0))` sits east of `θ u`, the tile `θ (u + (0, 1))` north of it.
**[choice]** `θ` is a map to tiles with values in `R`. -/
def TilesPlane (R : WangSet) : Prop :=
  ∃ θ : Plane → Tile, (∀ u, θ u ∈ R) ∧
    (∀ u, (θ u).E = (θ (u + (1, 0))).W) ∧ (∀ u, (θ u).N = (θ (u + (0, 1))).S)

/-! ## Sites of `ℤ⁶` (Section 2.2) -/

/-- Section 2.2: "We write a spatial site as `v = (u, P)`, where `u ∈ ℤ²` is planar and
`P ∈ ℤ⁴` is transverse." The site `(u, P)` of `ℤ⁶ = Fin 6 → ℤ` is
`(u.1, u.2, P 0, P 1, P 2, P 3)`.
**[choice]** The planar coordinates are the first two. -/
def site (u : Plane) (P : Fin 4 → ℤ) : UND.Site 6 :=
  Fin.cons (α := fun _ => ℤ) u.1 (Fin.cons (α := fun _ => ℤ) u.2 P)

/-! ## The five provider boxes (Section 2.3, display `nw:boxes`) -/

/-- (`nw:boxes`): the cluster corners `C_0 = 0` and `C_i = 160 e_i` (`1 ≤ i ≤ 4`).
**[choice]** The index set `{0, …, 4}` is `Option (Fin 4)`: `none` is `0`, `some i` is `i + 1`. -/
def corner : Option (Fin 4) → (Fin 4 → ℤ)
  | none => 0
  | some i => fun j => if j = i then 160 else 0

/-- (`nw:boxes`): a provider offset `a ∈ S = S_0 ∪ … ∪ S_4`, `S_i = C_i + {0, …, 15}⁴`, given by
its cluster and its position in the box. There are `q = 5·16⁴` of them; the boxes are disjoint, so
this indexing is a bijection onto `S`. -/
abbrev Provider := Option (Fin 4) × (Fin 4 → Fin 16)

/-- The offset `a = C_i + o ∈ ℤ⁴` of a provider. -/
def offset (π : Provider) : Fin 4 → ℤ := corner π.1 + fun j => ((π.2 j : ℕ) : ℤ)

/-! ## The alphabet and the cardinal checker (Section 2.2) -/

/-- Section 2.2: the alphabet `A_R = R ⊔ {⊥}`; `none` is the blank `⊥`, and `some r` is the live
letter `r ∈ R`. -/
abbrev Letter (R : WangSet) := Option R

/-- Section 2.2: "The cardinal checker `C_R` applied in a planar layer retains the central tile
precisely when all five letters at `u + Γ` are live and the four shared edges at `u` match",
`Γ = {0, ±e₁, ±e₂}`. `Keeps x v c`: the letter at `v` is the tile `c`, and the letters at the
east, west, north and south planar neighbours of `v` (same transverse coordinate) are live tiles
whose shared edges match those of `c`. -/
def Keeps {R : WangSet} (x : UND.Site 6 → Letter R) (v : UND.Site 6) (c : R) : Prop :=
  x v = some c ∧
    (∃ b : R, x (v + site (1, 0) 0) = some b ∧ c.1.E = b.1.W) ∧
    (∃ b : R, x (v + site (-1, 0) 0) = some b ∧ b.1.E = c.1.W) ∧
    (∃ b : R, x (v + site (0, 1) 0) = some b ∧ c.1.N = b.1.S) ∧
    (∃ b : R, x (v + site (0, -1) 0) = some b ∧ b.1.N = c.1.S)

open Classical in
/-- Section 2.2: the checked letter `y(v) = C_R(x(·, P))(u)` at `v = (u, P)`: the central letter
if the check passes, "otherwise it outputs `⊥`". -/
def check {R : WangSet} (x : UND.Site 6 → Letter R) (v : UND.Site 6) : Letter R :=
  if ∃ c, Keeps x v c then x v else none

/-- (`nw:rule`): the number `|{a ∈ S : y(u, P + a) = s}|` of providers whose checked reading at
`v = (u, P)` is the live letter `s`. -/
def votes {R : WangSet} (x : UND.Site 6 → Letter R) (v : UND.Site 6) (s : R) : ℕ :=
  (Finset.univ.filter fun π : Provider => check x (v + site 0 (offset π)) = some s).card

/-- (`nw:boxes`): the quorum `h = 4K = 4·16⁴`. -/
def quorum : ℕ := 4 * 16 ^ 4

open Classical in
/-- (`nw:rule`), the clustered quorum: `G_R(x)(u, P) = s` if `s ∈ R` and at least `h` of the `q`
checked readings `y(u, P + a)`, `a ∈ S`, equal `s`; `⊥` if no such live `s` exists.
**[choice]** The live letter is picked with `Classical.choose`; it is unique because
`2h = 8K > 5K = q` (paper, after (`nw:rule`)), so the choice is immaterial. -/
def natMap (R : WangSet) (x : UND.Site 6 → Letter R) : UND.Site 6 → Letter R := fun v =>
  if h : ∃ s : R, quorum ≤ votes x v s then some h.choose else none

/-! ## The automaton `G_R` on `ℤ⁶` -/

/-- Section 2.2: `Γ = {0, e₁, -e₁, e₂, -e₂}` (planar). -/
def cardinal : Finset Plane := {(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)}

/-- Section 2.3, after (`nw:rule`): "The actual neighbourhood is `Γ × S`." -/
def natNbhd : Finset (UND.Site 6) :=
  (cardinal ×ˢ (Finset.univ : Finset Provider)).image fun p => site p.1 (offset p.2)

/-- The identification of `A_R = R ⊔ {⊥}` with the symbol set `Fin |A_R|` of a `UND.CA`.
**[choice]** Any bijection would do (uniform replacement and ergodicity are invariant under
relabelling the alphabet); `Fintype.equivFin` is used, as for the noise-diagram core's rule. -/
def letterEquiv (R : WangSet) : Letter R ≃ Fin (Fintype.card (Letter R)) :=
  Fintype.equivFin (Letter R)

/-- **The rule `G_R`** (Section 2.3, (`nw:rule`)) as a cellular automaton on `ℤ⁶` with alphabet
`A_R = R ⊔ {⊥}` (through `letterEquiv`) and neighbourhood `Γ × S`: the local rule evaluates
`natMap R` at the origin on the pattern read on the neighbourhood.
**[choice]** Outside the neighbourhood the pattern is extended by `⊥`; `natMap R x 0` reads `x`
only on `Γ × S`, so the extension is immaterial (proved in `Rule/Bridge.lean`). -/
def natCA (R : WangSet) : UND.CA 6 where
  numSymbols := Fintype.card (Letter R)
  numSymbols_pos := Fintype.card_pos
  nbhd := natNbhd
  localRule pat := letterEquiv R (natMap R (fun z =>
    if h : z ∈ natNbhd then (letterEquiv R).symm (pat ⟨z, h⟩) else none) 0)

/-! ## The rate (`nw:constants`) -/

/-- (`nw:constants`): `ε_* = B^{-200}`, `B = 2Δ²`, `Δ = 18q`, `q = 5·16⁴`. -/
def epsStar : ℝ := (((2 * (18 * (5 * 16 ^ 4)) ^ 2 : ℕ) : ℝ) ^ 200)⁻¹

/-! ## Theorem D -/

/-- **Theorem D** (introduction; Theorem `nw:classification` without its coalescence bound): for
every finite Wang set `R` and every `0 < ε ≤ ε_*`, the rule `G_R` with uniform whole-symbol
replacement at rate `ε` is ergodic if and only if `R` does not tile `ℤ²`; and if `R` tiles, there
are two distinct translation-invariant stationary laws.
"Translation-invariant" is the noise-diagram core's `UND.CA.IsTranslationInvariant`: invariance
under every translation of `ℤ⁶`. This is exactly the paper's convention (Section 2.2, "Tiles,
configurations and noise": "Spatial translation invariance always means invariance under every
translation of `ℤ⁶`, unless a smaller group is explicitly named"), so the "spatially
translation-invariant" laws of Theorem `nw:classification` are invariant under all of `ℤ⁶`. The
two laws are probability measures (`UND.CA.HasTwoTIStationaryLaws`). -/
def NaturalClassification : Prop :=
  ∀ (R : WangSet) (ε : ℝ), 0 < ε → ε ≤ epsStar →
    ((natCA R).IsErgodic ε ↔ ¬ TilesPlane R) ∧
      (TilesPlane R → (natCA R).HasTwoTIStationaryLaws ε)

/-! ## Positive-rate automata (Theorem A: "the positive-rate automaton obtained from `G_{W_M}`") -/

/-- Section 2.2 (the noise): the law of `X_1(w)` given `X_0 = x`,
`(1 - ε) δ_{F(x)(w)} + ε · uniform`, for a cellular automaton `F` with uniform whole-symbol
replacement at rate `ε`. (The forgetting core's `FNE.siteLaw`, for an arbitrary automaton.) -/
def siteLaw {d : ℕ} (A : UND.CA d) (ε : ℝ) (x : A.Config) (w : UND.Site d) :
    MeasureTheory.Measure A.Sym :=
  ENNReal.ofReal (1 - ε) • MeasureTheory.Measure.dirac (A.apply x w) +
    ENNReal.ofReal ε • A.uniformLaw

/-- "The positive-rate automaton obtained from `G`": the cellular automaton `G` with uniform
whole-symbol replacement at rate `ε` is a probabilistic cellular automaton with positive rates.
Spelled out as in the forgetting core's `FNE.IsPositiveRatePCA`:
(i) the deterministic rule commutes with every translation of `ℤ^d`;
(ii) it is local, with the automaton's finite neighbourhood;
(iii) given `X_0 = x`, the values `X_1(w)` are independent with laws `siteLaw x w`;
(iv) every symbol has positive probability under every `siteLaw x w` ("positive rates").
**[choice]** The phrase "positive-rate automaton" is rendered by these four clauses, as for
`FNE.CorEight`. -/
def IsPositiveRatePCA {d : ℕ} (A : UND.CA d) (ε : ℝ) : Prop :=
  (∀ (a : UND.Site d) (x : A.Config), A.apply (A.shift a x) = A.shift a (A.apply x)) ∧
  (∀ (x x' : A.Config) (w : UND.Site d), (∀ z ∈ A.nbhd, x (w + z) = x' (w + z)) →
      A.apply x w = A.apply x' w) ∧
  (∀ x : A.Config, A.law ε (MeasureTheory.Measure.dirac x) 1 =
      MeasureTheory.Measure.infinitePi (fun w => siteLaw A ε x w)) ∧
  (∀ (x : A.Config) (w : UND.Site d) (s : A.Sym), 0 < siteLaw A ε x w {s})

/-! ## Theorem A on `ℤ⁶`, and the domino reduction -/

/-- **The classical domino reduction** (R. Berger, "The undecidability of
the domino problem", Mem. Amer. Math. Soc. 66 (1966); R. M. Robinson, "Undecidability and
nonperiodicity for tilings of the plane", Invent. Math. 12 (1971), 177–209). Paper, first
sentence of `nw:machine`: "There is a total computable map `M ↦ W_M` to finite Wang sets such that
`W_M` tiles if and only if `M` does not halt." Its proof: "Use the classical effective unseeded
domino reduction of Berger and Robinson, with translations of edge-coloured squares and no
distinguished origin tile. Its output tiles precisely on the nonhalting branch."
It is the one classical input of the paper's proof of Theorem A, and the hypothesis of the
conditional form `TheoremAFromDomino`. It is also proved here for the same machine model, through
the forgetting core's family `R_M` (Theorem C): `FNR.domino_reduction` in `Reduction.lean`.
**[choice]** Machines, the blank-tape start and halting are the forgetting core's
(`FNE.TuringMachine`, `FNE.TuringMachine.Halts`), as in `FNE.CorEight`; a finite Wang set is
computed as a list of tiles, the Wang set being the set of its entries (`Finset` has no
`Primcodable` instance; as in `FNE.CorEight`); tiling is `TilesPlane` (translations only, no
distinguished origin tile). -/
def DominoReduction : Prop :=
  ∃ W : TuringMachine → List Tile, Computable W ∧
    ∀ M : TuringMachine, TilesPlane (W M).toFinset ↔ ¬ M.Halts

/-- The printed statement of **Theorem A** (introduction, `mainA`; `nw:machine`): "There is a total
computable map `M ↦ W_M` from Turing machines to finite Wang sets such that, for every
`ε ∈ (0, ε_*]`, the positive-rate automaton obtained from `G_{W_M}` is ergodic if and only if `M`
halts."
**[choice]** As in `FNE.CorEight`: a Wang set is computed as a list of tiles; computability of
`M ↦ G_{W_M}` is rendered as computability of `M ↦ W_M` (the rule `natCA` is an explicit finite
construction from the tiles); "the positive-rate automaton obtained from `G_{W_M}`" is `G_{W_M}`
with uniform whole-symbol replacement at rate `ε`, and its positive-rate property is stated
(`IsPositiveRatePCA`). -/
def ErgodicityReduction : Prop :=
  ∃ W : TuringMachine → List Tile, Computable W ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ epsStar → ∀ M : TuringMachine,
      IsPositiveRatePCA (natCA (W M).toFinset) ε ∧
        ((natCA (W M).toFinset).IsErgodic ε ↔ M.Halts)

/-- **Theorem A on `ℤ⁶`** (introduction, `mainA`; Corollary `nw:machine`), as printed: no
hypothesis. -/
def TheoremA : Prop := ErgodicityReduction

/-- Theorem A from its one classical input, the domino reduction of Berger and Robinson: the route
of the paper's proof of `nw:machine` ("The only undecidability input in this route is the
classical domino reduction of Berger and Robinson"). A conditional form, weaker than `TheoremA`;
not a printed statement. -/
def TheoremAFromDomino : Prop := DominoReduction → ErgodicityReduction

/-! ## The undecidability form (a corollary; session 1) -/

/-- **Berger's theorem (1966; Robinson 1971): the domino problem is undecidable.** "There is no
algorithm which decides, for an arbitrary finite set of Wang tiles (dominoes), whether it admits a
tiling of the plane" (translations only, no distinguished origin tile).
**[choice]** An algorithm is a computable function in Mathlib's sense; a finite Wang set is given
to it as a list of tiles (as in the forgetting core's `FNE.CorEight`: `Finset` has no
`Primcodable` instance), the Wang set being the set of its entries. -/
def DominoUndecidable : Prop :=
  ¬ ∃ g : List Tile → Bool, Computable g ∧
    ∀ l : List Tile, g l = true ↔ TilesPlane l.toFinset

/-- No algorithm decides, given `R` (as a list of tiles), whether `G_R` is ergodic at the rate
`ε`. -/
def ErgodicityUndecidable (ε : ℝ) : Prop :=
  ¬ ∃ g : List Tile → Bool, Computable g ∧
    ∀ l : List Tile, g l = true ↔ (natCA l.toFinset).IsErgodic ε

/-- **The undecidability form** (a corollary of Theorem D; the last sentence of `nw:machine`, "In
particular ergodicity is undecidable at each one of these fixed rates", for the raw inputs `R`):
under Berger's theorem, at every fixed rate `0 < ε ≤ ε_*` ergodicity of `G_R` is undecidable in
`R`. Not a printed environment; kept from session 1. -/
def TheoremAUndecidable : Prop :=
  DominoUndecidable → ∀ ε : ℝ, 0 < ε → ε ≤ epsStar → ErgodicityUndecidable ε

/-! ## Corollary `nw:machine` in full -/

/-- **Corollary `nw:machine`** (Section 3, "Theorem A on `ℤ⁶`"), its three sentences: "There is
a total computable map `M ↦ W_M` to finite Wang sets such that `W_M` tiles if and only if `M`
does not halt. For every `ε ∈ (0, ε_*]`, `G_{W_M}` with uniform replacement is a positive-rate PCA
on `ℤ⁶` that is ergodic if and only if `M` halts. In particular ergodicity is undecidable at each
one of these fixed rates."
**[choice]** As in `ErgodicityReduction`; "undecidable" for this family: no computable
`g : TuringMachine → Bool` decides whether `G_{W_M}` is ergodic at the rate `ε` (in the style of
`DominoUndecidable`). -/
def MachineCorollary : Prop :=
  ∃ W : TuringMachine → List Tile, Computable W ∧
    (∀ M : TuringMachine, TilesPlane (W M).toFinset ↔ ¬ M.Halts) ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ epsStar →
      (∀ M : TuringMachine, IsPositiveRatePCA (natCA (W M).toFinset) ε ∧
        ((natCA (W M).toFinset).IsErgodic ε ↔ M.Halts)) ∧
      ¬ ∃ g : TuringMachine → Bool, Computable g ∧
        ∀ M : TuringMachine, g M = true ↔ (natCA (W M).toFinset).IsErgodic ε

end FNR
-- END verbatim copy of ForgettingNaturalRule/Statements.lean
end

/-! ## 5. The frozen Z4 statement file -/

run_cmd Lean.modifyEnv (fun env => env.setMainModule `ForgettingLower.Statements)
run_cmd Lean.modifyEnv (fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {})

-- BEGIN verbatim copy of ForgettingLower/Statements.lean (the whole file except its import lines)
/-
# Statement file — FROZEN (12 Nov 2026): Section 12, Theorem 12.5 (ld:z4), v2.0.0

Frozen after the blind fidelity read and QB rulings of 12 Nov 2026.
The sha256 in STATUS.md is the statement of record; this file never changes again.
Source: fixed-noise-ergodicity-release/paper/sections/12-lower-dimensions.tex.

REUSE: FNE.Tile/WangSet/Plane/TuringMachine/Halts, FNR.TilesPlane and Letter,
UND.CA (including the actual uniform whole-symbol noise, probability laws,
IsStationary, IsErgodic and FNE.WeakTendsto), FNR.IsPositiveRatePCA.
ADAPT: the transparent FNR cardinal-checker/quorum construction, with two
transverse coordinates, three boxes and h = 512. The first two coordinates
of UND.Site 4 are planar. Option (Fin 2) indexes clusters 0,1,2.

Only target propositions are stated here; their proofs live in the proof files.
**[choice]** Inherited encodings (natural-number tile colours, list-coded raw inputs,
the FNE machine model and UND noise time indexing) are reused verbatim from the frozen cores.
-/

set_option autoImplicit false

noncomputable section

namespace FLD

open FNE (Tile WangSet Plane TuringMachine)
open MeasureTheory

/-- Tiling with translations only, no distinguished tile; exactly FNR's predicate.
**[choice]** Reuse its map-to-tiles encoding with membership in R. -/
abbrev TilesPlane := FNR.TilesPlane

/-- ld:constants: one cluster contains K = 16² offsets. -/
def K : ℕ := 16 ^ 2
/-- ld:constants: three clusters. -/
def q : ℕ := 3 * K
/-- Bound on the undirected ordinary degree, using |Λ| = 9. -/
def Delta : ℕ := 18 * q
/-- The connected-edge encoding base 2Δ². -/
def B : ℕ := 2 * Delta ^ 2
/-- The transverse l1 diameter of S. -/
def D : ℕ := 350
/-- The all-path marked-parent density cutoff. -/
def delta : ℝ := 1 / (4 * ((D : ℝ) + 1))
/-- Integer cost per flag of the whole path, spurs and contours. -/
def densityCost : ℕ := 16860
/-- The single rational rate, independent of R. -/
def eps0Rat : ℚ := ((382205952 : ℚ) ^ 33720)⁻¹
/-- ld:constants: e₀ = 382205952^(-33720), exactly as printed. -/
def eps0 : ℝ := ((382205952 : ℝ) ^ 33720)⁻¹

/- The following definitions adapt FNR's statement definitions. `site` is
(u₁,u₂,P₁,P₂); `corner none = 0`, `corner (some j) = 160 e_j`;
Provider indexes S₀ ⊔ S₁ ⊔ S₂, and offset is corner + {0,...,15}².
Keeps checks all five live cardinal letters and the four oriented edges.
check keeps the central tile iff Keeps holds. natMap takes a live quorum
of 512 votes, or blank. natNbhd = Γ × S is independent of R.
letterEquiv reuses the existing alphabet bijection. natCA evaluates the
rule on its neighbourhood; the extension by blank is immaterial by locality.
-/
/-- Section 12: site (u,P) in Z4.
**[choice]** The planar coordinates come first. -/
def site (u : Plane) (P : Fin 2 → ℤ) : UND.Site 4 :=
  Fin.cons (α := fun _ => ℤ) u.1 (Fin.cons (α := fun _ => ℤ) u.2 P)

/-! ## The three provider boxes (Section 12, ld:constants) -/

/-- ld:constants: the corners 0, 160e1, 160e2.
**[choice]** Option (Fin 2) labels clusters: none is 0, some 0 is 1, some 1 is 2. -/
def corner : Option (Fin 2) → (Fin 2 → ℤ)
  | none => 0
  | some i => fun j => if j = i then 160 else 0

/-- Three indexed boxes, each with 16 squared offsets. -/
abbrev Provider := Option (Fin 2) × (Fin 2 → Fin 16)

/-- The physical provider offset in its indexed box. -/
def offset (π : Provider) : Fin 2 → ℤ := corner π.1 + fun j => ((π.2 j : ℕ) : ℤ)

/-- The explicit finite box S_c = corner c + {0,...,15} squared. -/
def providerBox (c : Option (Fin 2)) : Finset (Fin 2 → ℤ) :=
  (Finset.univ : Finset (Fin 2 → Fin 16)).image fun o => offset (c, o)
/-- S0 = {0,...,15} squared. -/
def S0 : Finset (Fin 2 → ℤ) := providerBox none
/-- S1 = 160e1 + S0. -/
def S1 : Finset (Fin 2 → ℤ) := providerBox (some 0)
/-- S2 = 160e2 + S0. -/
def S2 : Finset (Fin 2 → ℤ) := providerBox (some 1)
/-- The union of all three provider boxes, indexed by Provider. -/
def S : Finset (Fin 2 → ℤ) := (Finset.univ : Finset Provider).image offset

/-! ## The alphabet and cardinal checker (Section 12, natural rule) -/

abbrev Letter (R : WangSet) := FNR.Letter R

/-- Section 12: five live cardinal readings with matching shared edges. -/
def Keeps {R : WangSet} (x : UND.Site 4 → Letter R) (v : UND.Site 4) (c : R) : Prop :=
  x v = some c ∧
    (∃ b : R, x (v + site (1, 0) 0) = some b ∧ c.1.E = b.1.W) ∧
    (∃ b : R, x (v + site (-1, 0) 0) = some b ∧ b.1.E = c.1.W) ∧
    (∃ b : R, x (v + site (0, 1) 0) = some b ∧ c.1.N = b.1.S) ∧
    (∃ b : R, x (v + site (0, -1) 0) = some b ∧ b.1.N = c.1.S)

open Classical in
/-- Section 12: keep the centre exactly when its cardinal check passes. -/
def check {R : WangSet} (x : UND.Site 4 → Letter R) (v : UND.Site 4) : Letter R :=
  if ∃ c, Keeps x v c then x v else none

/-- The number of checked providers voting for a specified live tile. -/
def votes {R : WangSet} (x : UND.Site 4 → Letter R) (v : UND.Site 4) (s : R) : ℕ :=
  (Finset.univ.filter fun π : Provider => check x (v + site 0 (offset π)) = some s).card

/-- ld:constants: h = 2K = 512. -/
def quorum : ℕ := 2 * 16 ^ 2

open Classical in
/-- G_R^(4): the unique live quorum tile if present, otherwise blank.
**[choice]** Classical.choose selects the tile; 2 * 512 > 768 makes it unique. -/
def natMap (R : WangSet) (x : UND.Site 4 → Letter R) : UND.Site 4 → Letter R := fun v =>
  if h : ∃ s : R, quorum ≤ votes x v s then some h.choose else none

/-! ## The automaton `G_R` on `ℤ⁴` -/

abbrev cardinal : Finset Plane := FNR.cardinal

/-- Section 12: the common neighbourhood Gamma times S. -/
def natNbhd : Finset (UND.Site 4) :=
  (cardinal ×ˢ (Finset.univ : Finset Provider)).image fun p => site p.1 (offset p.2)

/-- Reuse FNR's bijection from R plus blank to the finite symbol alphabet.
**[choice]** Fintype.equivFin relabels Option R as Fin |Option R|. -/
def letterEquiv (R : WangSet) : Letter R ≃ Fin (Fintype.card (Letter R)) :=
  FNR.letterEquiv R

/-- The explicit Z4 automaton, evaluated through its finite neighbourhood.
**[choice]** Extend the pattern by blank outside natNbhd; those values are never read. -/
def natCA (R : WangSet) : UND.CA 4 where
  numSymbols := Fintype.card (Letter R)
  numSymbols_pos := Fintype.card_pos
  nbhd := natNbhd
  localRule pat := letterEquiv R (natMap R (fun z =>
    if h : z ∈ natNbhd then (letterEquiv R).symm (pat ⟨z, h⟩) else none) 0)


/-- Exactly the printed two distinct invariant probability laws; no spatial
translation-invariance condition is added to Theorem 12.5. -/
def HasTwoInvariantLaws {d : ℕ} (A : UND.CA d) (e : ℝ) : Prop :=
  ∃ μ ν : Measure A.Config, μ ≠ ν ∧
    IsProbabilityMeasure μ ∧ A.IsStationary e μ ∧
    IsProbabilityMeasure ν ∧ A.IsStationary e ν

/-- Finite-window coupling from the past, simultaneously for all finite windows,
all observation times, all sufficiently remote past horizons and all starts.
This uses UND.CA.flow and the existing two-sided iid noise measure verbatim.
**[choice]** The added forall t is equivalent to the printed per-window form
by countability of the time and finite-window index sets; it goes beyond the printed words. -/
def AllTimeCFTP {d : ℕ} (A : UND.CA d) (e : ℝ) : Prop :=
  ∀ᵐ ω ∂(A.noiseLaw₂ e), ∀ t : ℤ, ∀ O : Finset (UND.Site d),
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x y : A.Config, ∀ w ∈ O,
      A.flow ω (t - (n : ℤ)) n x w = A.flow ω (t - (n : ℤ)) n y w

/-- Theorem 12.5 (ld:z4), every sentence. IsErgodic already states existence
and uniqueness of an invariant probability law AND weak convergence from every
initial probability law. The non-tiling clause repeats it next to CFTP so that
this printed sentence remains explicit. Constants and natNbhd are global
transparent definitions independent of R; the common-neighbourhood clause is
included literally. No convergence rate or Gibbs consequence is asserted.
**[choice]** Ergodicity is repeated in the non-tiling clause to retain that printed sentence. -/
def Z4Classification : Prop :=
  (∀ R : WangSet, (natCA R).nbhd = natNbhd) ∧
  ∀ (R : WangSet) (e : ℝ), 0 < e → e ≤ eps0 →
    ((natCA R).IsErgodic e ↔ ¬ TilesPlane R) ∧
    (TilesPlane R → HasTwoInvariantLaws (natCA R) e) ∧
    (¬ TilesPlane R → AllTimeCFTP (natCA R) e ∧ (natCA R).IsErgodic e)

/-- The direct Z⁴ undecidability corollary. Same computable W for all allowed
rates, with its domino specification, positive-rate property, classification,
and no computable decider at any one fixed allowed rate. Machines and list
codes are exactly FNR's, so FNR.domino_reduction applies with no hypotheses.
**[choice]** This strengthens the printed last sentence: every allowed rate,
the machine-indexed subfamily and a positive-rate clause. It implies Z4RawUndecidable. -/
def Z4MachineCorollary : Prop :=
  ∃ W : TuringMachine → List Tile, Computable W ∧
    (∀ M : TuringMachine, TilesPlane (W M).toFinset ↔ ¬ M.Halts) ∧
    ∀ e : ℝ, 0 < e → e ≤ eps0 →
      (∀ M : TuringMachine, FNR.IsPositiveRatePCA (natCA (W M).toFinset) e ∧
        ((natCA (W M).toFinset).IsErgodic e ↔ M.Halts)) ∧
      ¬ ∃ g : TuringMachine → Bool, Computable g ∧
        ∀ M : TuringMachine, g M = true ↔ (natCA (W M).toFinset).IsErgodic e

/-- Proof of Theorem 12.5, last sentence: fixed-rate undecidability on the raw family
R ↦ G_R^(4) (abstract: "one explicit positive rational replacement rate ... makes ergodicity
undecidable"). Raw inputs are lists of tiles, as in FNR.ErgodicityUndecidable; no hypothesis. -/
def Z4RawUndecidable : Prop :=
  ∀ e : ℝ, 0 < e → e ≤ eps0 →
    ¬ ∃ g : List Tile → Bool, Computable g ∧
      ∀ l : List Tile, g l = true ↔ (natCA l.toFinset).IsErgodic e

end FLD
-- END verbatim copy of ForgettingLower/Statements.lean
end

/-! ## The three holes (the release targets) -/

run_cmd Lean.modifyEnv (fun env => env.setMainModule `Challenge)

namespace FLD

theorem z4_classification : Z4Classification := by sorry

theorem z4_machine_corollary : Z4MachineCorollary := by sorry

theorem z4_raw_undecidable : Z4RawUndecidable := by sorry

end FLD
