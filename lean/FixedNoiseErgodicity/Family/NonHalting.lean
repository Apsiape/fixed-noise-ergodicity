/-
# Theorem A, non-halting half, for the paper's family `R_M`

`prop:tiles` (`tiles_of_not_halts`) with `thm:memory` and `set:memory-nonergodic`
(`not_ergodic_of_tiles`): if `M` does not halt, the noisy quorum rule `F^[6]_{R_M}` on `ℤ⁸` is not
ergodic, for every `0 < ε ≤ ε₀`. Unconditional for the explicit family `familyR` of `def:family`.
-/
import FixedNoiseErgodicity.Family.FamilyR
import FixedNoiseErgodicity.Section4.Memory

set_option autoImplicit false

namespace FNE.Family

open FNE

/-- **Theorem A, non-halting half, for `R_M`.** If `M` does not halt, then for every
`0 < ε ≤ ε₀` the noisy quorum rule `F^[6]_{R_M}` with uniform replacement at rate `ε` is not
ergodic. -/
theorem not_ergodic_familyR (M : TuringMachine) (hM : ¬ M.Halts) {ε : ℝ} (h0 : 0 < ε)
    (hε : ε ≤ eps0) : ¬ IsErgodic 6 (familyR M).toFinset ε := by
  rw [eps0_eq_epsK] at hε
  exact not_ergodic_of_tiles (by norm_num) h0 hε (tiles_of_not_halts M hM)

end FNE.Family
