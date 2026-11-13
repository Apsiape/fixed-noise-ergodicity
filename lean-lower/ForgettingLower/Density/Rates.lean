/- Rate slack for the density argument, without expanding the exact denominator. -/
import ForgettingLower.Constants

set_option autoImplicit false

namespace FLD.Const

/-- The entropy-cost factor times the allowed noise is at most B^(-16860). -/
theorem density_base_le {e : ℝ} (he : e ≤ eps0) :
    (B : ℝ) ^ densityCost * e ≤ ((B : ℝ) ^ densityCost)⁻¹ := by
  have hb : (B : ℝ) ≠ 0 := by rw [B_eq]; norm_num
  calc (B : ℝ) ^ densityCost * e ≤ (B : ℝ) ^ densityCost * eps0 :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((B : ℝ) ^ densityCost)⁻¹ := by
      rw [eps0_eq_B, Nat.mul_comm 2 densityCost, pow_mul]
      field_simp

/-- The printed rate has ample geometric-series slack. -/
theorem inv_densityCost_lt_quarter : ((B : ℝ) ^ densityCost)⁻¹ < 1 / 4 := by
  have hb : (4 : ℝ) < B := by rw [B_eq]; norm_num
  have ht : (B : ℝ) ≤ (B : ℝ) ^ densityCost := by
    simpa using (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ B)
      (by norm_num [densityCost] : 1 ≤ densityCost))
  apply (inv_lt_iff_one_lt_mul₀ (by positivity : (0 : ℝ) < (B : ℝ) ^ densityCost)).mpr
  nlinarith

theorem density_base_lt_quarter {e : ℝ} (he : e ≤ eps0) :
    (B : ℝ) ^ densityCost * e < 1 / 4 :=
  (density_base_le he).trans_lt inv_densityCost_lt_quarter

end FLD.Const
