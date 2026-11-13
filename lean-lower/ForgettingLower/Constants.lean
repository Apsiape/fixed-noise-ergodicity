import ForgettingLower.Statements

set_option autoImplicit false

namespace FLD.Const

theorem K_eq : K = 256 := by norm_num [K]
theorem q_eq : q = 768 := by norm_num [q, K]
theorem quorum_eq : quorum = 512 := by norm_num [quorum]
theorem Delta_eq : Delta = 13824 := by norm_num [Delta, q, K]
theorem B_eq : B = 382205952 := by norm_num [B, Delta, q, K]
theorem delta_eq : delta = (1 : ℝ) / 1404 := by norm_num [delta, D]
theorem densityCost_eq : densityCost = 16860 := rfl

/-- The cutoff is positive without expanding its large exact denominator. -/
theorem eps0_pos : 0 < eps0 := by unfold eps0; positivity

/-- The cutoff is a legal noise probability. -/
theorem eps0_le_one : eps0 ≤ 1 := by
  unfold eps0
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 382205952))

/-- The printed rate is the image of a single positive rational. -/
theorem eps0Rat_cast : (eps0Rat : ℝ) = eps0 := by
  simp only [eps0Rat, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat, eps0]

/-- The two equivalent printed forms of e0 agree exactly. -/
theorem eps0_eq_B : eps0 = ((B : ℝ) ^ (2 * densityCost))⁻¹ := by
  rw [B_eq]
  rfl

/-- The path union cost is 12/delta +12. -/
theorem densityCost_formula : (densityCost : ℝ) = 12 / delta + 12 := by
  norm_num [densityCost, delta, D]

/-- The two-path drift margin is exactly one half. -/
theorem drift_margin : 2 * delta * ((D : ℝ) + 1) = 1 / 2 := by
  norm_num [delta, D]

end FLD.Const
