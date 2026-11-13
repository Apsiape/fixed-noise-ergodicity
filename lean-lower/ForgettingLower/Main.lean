/- Theorem 12.5: every clause of the frozen dimension-four classification. -/
import ForgettingLower.Forget.CFTP
import ForgettingLower.Memory.Invariant
import ForgettingLower.Density.Entropy

set_option autoImplicit false

namespace FLD

/-- The neighbourhood is literally common to every R. -/
theorem common_neighbourhood (R : FNE.WangSet) : (natCA R).nbhd = natNbhd := rfl

/-- Theorem 12.5, exactly the frozen proposition, with no named assumptions. -/
theorem z4_classification : Z4Classification := by
  refine ⟨common_neighbourhood, fun R e hpos he => ?_⟩
  exact ⟨⟨fun herg ht => Memory.memory_branch ht hpos.le he herg,
    fun hnt => Forget.ergodic_of_not_tiles hnt hpos.le he⟩,
    fun ht => Memory.twoInvariant_of_tiles ht hpos.le he,
    fun hnt => ⟨Forget.allTimeCFTP_of_not_tiles hnt hpos.le he,
      Forget.ergodic_of_not_tiles hnt hpos.le he⟩⟩

end FLD
