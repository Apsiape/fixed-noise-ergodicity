/-
# The final theorem: Corollary `cor:eight` (Theorem A on `ℤ⁸`)

`Statements.lean` states the corollary as the proposition `CorEight` (a ruling of session 9:
the statement file keeps the printed statement byte for byte; the proof lives here, in a file that
imports every part of the formalization). The proof: the family `R_M` of `def:family`
(`familyR`, `Family/FamilyR.lean`) is computable (`computable_familyR`, Section 8,
`Family/Computable.lean`), so `cor_eight_of_computable` (`Three/Assembly.lean`: Theorem C with
`thm:three` and `prop:tiles`, and Theorem B for the noise half) gives the statement.
-/
import FixedNoiseErgodicity.Three.Assembly
import FixedNoiseErgodicity.Family.Computable

set_option autoImplicit false

namespace FNE

/-- **Corollary `cor:eight` (Theorem A on `ℤ⁸`).** For every `ε ∈ (0, ε₀]`, `ε₀ = 490000^(-99)`,
and every Turing machine `M`, the noisy quorum rule `F^[6]_{R_M}` on `ℤ⁸` with uniform replacement
at rate `ε` is a positive-rate probabilistic cellular automaton, ergodic if and only if `M` halts;
and `M ↦ R_M` is total computable. The statement is `CorEight` of `Statements.lean`. -/
theorem cor_eight : CorEight :=
  Three.cor_eight_of_computable Family.computable_familyR

end FNE
