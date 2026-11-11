/-
# "Undecidable" as a theorem (decision D1, completed in session 10)

The title of the paper says that forgetting under noise is undecidable. `cor:eight`
(`FNE.cor_eight`, `Main.lean`) says that the noisy quorum rule `F^[6]_{R_M}` is ergodic iff the
machine `M` halts. This file turns "undecidable" into theorems in Mathlib's own sense
(`ComputablePred`, `REPred` of `Mathlib.Computability`), from Mathlib's halting theorems
(`ComputablePred.halting_problem`, `ComputablePred.halting_problem_not_re`) through the compiler of
`Compiler/Universal.lean` (`compiler : Nat.Partrec.Code → TuringMachine`, computable, `compiler c`
halts iff `c` halts on input `0`). No axiom and no hypothesis is added: Mathlib's theorems are used
as theorems.

In words:
* **`halts_not_computable`**: no computable predicate decides whether a list-encoded Turing
  machine (`TuringMachine`, started on a blank tape) halts; **`not_halts_not_re`**: the machines
  that do not halt do not even form a recursively enumerable set.
* **`cor_eight_undecidable`**: for every noise rate `ε` with `0 < ε ≤ ε₀`, no computable predicate
  of the machine `M` decides whether `F^[6]_{R_M}` (the noisy quorum rule of the paper's family
  `R_M` on `ℤ⁸`, uniform replacement at rate `ε`) is ergodic; **`nonergodic_not_re`**: the machines
  `M` for which it is not ergodic do not form a recursively enumerable set.
* **`cor_eight_undecidable_statement`**: the statement of `cor:eight` with "undecidable" added, in
  the vocabulary of `Statements.lean` only: there is a total computable map `M ↦ R_M` from
  machines to finite Wang sets such that, for every `ε ∈ (0, ε₀]`, every `F^[6]_{R_M}` is a
  positive-rate PCA, it is ergodic iff `M` halts, and ergodicity of `F^[6]_{R_M}` is not a
  computable predicate of `M` (nor is non-ergodicity recursively enumerable).

**[choice]** "Undecidable" is rendered as Mathlib's `¬ ComputablePred` (no total computable
Boolean function decides the predicate), for each fixed admissible `ε`, with machines coded by the
`Primcodable TuringMachine` instance of `Statements.lean` (tables and halting lists as lists of
natural numbers). The `¬ REPred` clauses for the complements are a strengthening (non-halting and
non-ergodicity are not even semi-decidable).
-/
import FixedNoiseErgodicity.Bridge
import FixedNoiseErgodicity.Compiler.Universal

set_option autoImplicit false

namespace FNE

open Nat.Partrec

/-- **Halting is undecidable** for the list-encoded machines: no computable predicate decides
`TuringMachine.Halts`. From Mathlib's `ComputablePred.halting_problem` through the computable
compiler `Compiler.compiler`. -/
theorem halts_not_computable : ¬ ComputablePred TuringMachine.Halts :=
  not_computable_halts_of_compiler Compiler.compiler Compiler.computable_compiler
    Compiler.compiler_halts

/-- **Non-halting is not recursively enumerable** for the list-encoded machines (from Mathlib's
`ComputablePred.halting_problem_not_re`). -/
theorem not_halts_not_re : ¬ REPred fun M : TuringMachine => ¬ M.Halts := fun h => by
  have h' : REPred fun c : Code => ¬ (Compiler.compiler c).Halts :=
    h.comp Compiler.computable_compiler
  exact ComputablePred.halting_problem_not_re 0
    (h'.of_eq fun c => by rw [Compiler.compiler_halts])

/-- **Ergodicity is undecidable (`cor:eight`, "undecidable").** For every `ε` with
`0 < ε ≤ ε₀ = 490000^(-99)`, no computable predicate of the Turing machine `M` decides whether the
noisy quorum rule `F^[6]_{R_M}` on `ℤ⁸`, with uniform replacement at rate `ε`, is ergodic. -/
theorem cor_eight_undecidable {ε : ℝ} (h0 : 0 < ε) (hε : ε ≤ eps0) :
    ¬ ComputablePred fun M : TuringMachine => IsErgodic 6 (Family.familyR M).toFinset ε :=
  not_computable_ergodic h0 hε halts_not_computable

/-- **Non-ergodicity is not even recursively enumerable.** For every `0 < ε ≤ ε₀`, the machines `M`
for which `F^[6]_{R_M}` is not ergodic do not form a recursively enumerable set. -/
theorem nonergodic_not_re {ε : ℝ} (h0 : 0 < ε) (hε : ε ≤ eps0) :
    ¬ REPred fun M : TuringMachine => ¬ IsErgodic 6 (Family.familyR M).toFinset ε := fun h =>
  not_halts_not_re (h.of_eq fun M => by rw [(Three.eight_familyR h0 hε M).2])

/-- **`cor:eight` with "undecidable", in the vocabulary of `Statements.lean`.** There is a total
computable map `M ↦ R_M` from Turing machines to finite Wang sets such that for every
`ε ∈ (0, ε₀]`: for every machine `M`, the noisy quorum rule `F^[6]_{R_M}` on `ℤ⁸` with uniform
replacement at rate `ε` is a positive-rate probabilistic cellular automaton, ergodic if and only if
`M` halts; no computable predicate of `M` decides whether `F^[6]_{R_M}` is ergodic; and the
machines for which it is not ergodic do not form a recursively enumerable set. -/
theorem cor_eight_undecidable_statement :
    ∃ Rfam : TuringMachine → List Tile, Computable Rfam ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ eps0 →
        (∀ M : TuringMachine, IsPositiveRatePCA 6 (Rfam M).toFinset ε ∧
          (IsErgodic 6 (Rfam M).toFinset ε ↔ M.Halts)) ∧
        ¬ ComputablePred (fun M : TuringMachine => IsErgodic 6 (Rfam M).toFinset ε) ∧
        ¬ REPred (fun M : TuringMachine => ¬ IsErgodic 6 (Rfam M).toFinset ε) := by
  obtain ⟨Rfam, hc, h⟩ := cor_eight
  refine ⟨Rfam, hc, fun ε h0 hε => ⟨h ε h0 hε, ?_, ?_⟩⟩
  · exact not_computable_ergodic_of (fun M => (h ε h0 hε M).2) halts_not_computable
  · intro hre
    exact not_halts_not_re (hre.of_eq fun M => by rw [(h ε h0 hε M).2])

end FNE
