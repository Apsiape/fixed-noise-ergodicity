/- Density D3 leaf: sum the encodings over every allowed edge count, including 0. -/
import ForgettingLower.Density.Slabs

set_option autoImplicit false

namespace FLD.Density

open scoped BigOperators

/-- If a rooted connected n-edge union with a terminal subset has at most 2b^n
encodings, summing over ALL edge counts 0 through m costs at most 4b^m. -/
theorem encoding_sum_le (b : ℕ) (hb : 2 ≤ b) (m : ℕ) :
    (∑ n ∈ Finset.range (m + 1), 2 * b ^ n) ≤ 4 * b ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h : 4 * b ^ m ≤ 2 * b ^ (m + 1) := by
      have := Nat.mul_le_mul_left (2 * b ^ m) hb
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
    omega

end FLD.Density
