/-
# The constants (`fgt:rem-constants`, the proof of `thm:memory`, `pf:threshold`)

`q = k + 1`, `a = 2q² + 1`, `D₀ = 50q`, `ε_k = (4 D₀²)^(-a)`; the forgetting rate
`β = 2 D₀² ε^{1/a}` and the memory rate `λ = 2 D₀² ε^{1/q²}`.
* `fgt:rem-constants`: if `0 < ε ≤ ε_k` then `β ≤ 1/2` (`beta_le_half`);
* proof of `thm:memory`: if moreover `k ≥ 2` then `λ ≤ 1/(8 D₀²) ≤ 1/180000` (`lam_le`), hence
  `ε (1 + 2λ/(1 - λ)) < 1.01 ε` (`memoryBound_lt`);
* `ε₀ = ε_6` (`eps0_eq_epsK`).
-/
import FixedNoiseErgodicity.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

noncomputable section

namespace FNE

/-- `fgt:rem-constants`: the rate `ε_k = (4 D₀²)^(-a)`, with `q = k + 1`, `a = 2q² + 1` and
`D₀ = 50q`. -/
def epsK (k : ℕ) : ℝ := ((4 * (50 * ((k : ℝ) + 1)) ^ 2) ^ (2 * (k + 1) ^ 2 + 1))⁻¹

/-- `thm:forgetting`: the rate `β = 2 D₀² ε^{1/a}`. -/
def beta (k : ℕ) (ε : ℝ) : ℝ :=
  2 * (50 * ((k : ℝ) + 1)) ^ 2 * ε ^ (1 / (2 * ((k : ℝ) + 1) ^ 2 + 1))

/-- `thm:memory`: the rate `λ = 2 D₀² ε^{1/q²}`. -/
def lam (k : ℕ) (ε : ℝ) : ℝ := 2 * (50 * ((k : ℝ) + 1)) ^ 2 * ε ^ (1 / ((k : ℝ) + 1) ^ 2)

/-- `cor:eight` uses `ε₀ = ε_6`. -/
theorem eps0_eq_epsK : eps0 = epsK 6 := by
  unfold eps0 epsK
  norm_num

theorem epsK_pos (k : ℕ) : 0 < epsK k := by
  unfold epsK
  positivity

theorem epsK_le_one (k : ℕ) : epsK k ≤ 1 := by
  unfold epsK
  refine inv_le_one_of_one_le₀ (one_le_pow₀ ?_)
  have : (1 : ℝ) ≤ 50 * ((k : ℝ) + 1) := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  nlinarith

theorem beta_nonneg (k : ℕ) {ε : ℝ} (h0 : 0 ≤ ε) : 0 ≤ beta k ε := by
  unfold beta
  positivity

theorem lam_nonneg (k : ℕ) {ε : ℝ} (h0 : 0 ≤ ε) : 0 ≤ lam k ε := by
  unfold lam
  positivity

/-- For `0 < ε ≤ ε_k` and `b > 0`: `ε^{1/b} ≤ ((4 D₀²)^{a/b})⁻¹`. -/
theorem rpow_le_of_le_epsK {k : ℕ} {ε : ℝ} (h0 : 0 < ε) (hε : ε ≤ epsK k) {b : ℝ} (hb : 0 < b) :
    ε ^ (1 / b) ≤
      ((4 * (50 * ((k : ℝ) + 1)) ^ 2) ^ ((2 * ((k : ℝ) + 1) ^ 2 + 1) / b))⁻¹ := by
  have hB : (0 : ℝ) ≤ 4 * (50 * ((k : ℝ) + 1)) ^ 2 := by positivity
  refine (Real.rpow_le_rpow h0.le hε (by positivity)).trans_eq ?_
  unfold epsK
  rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hB]
  congr 2
  push_cast
  ring

/-- **`fgt:rem-constants`.** If `0 < ε ≤ ε_k`, then `β = 2 D₀² ε^{1/a} ≤ 1/2`. -/
theorem beta_le_half {k : ℕ} {ε : ℝ} (h0 : 0 < ε) (hε : ε ≤ epsK k) : beta k ε ≤ 1 / 2 := by
  have ha : (0 : ℝ) < 2 * ((k : ℝ) + 1) ^ 2 + 1 := by positivity
  have hD : (0 : ℝ) < 50 * ((k : ℝ) + 1) := by positivity
  have h := rpow_le_of_le_epsK h0 hε ha
  rw [div_self ha.ne', Real.rpow_one] at h
  unfold beta
  calc 2 * (50 * ((k : ℝ) + 1)) ^ 2 * ε ^ (1 / (2 * ((k : ℝ) + 1) ^ 2 + 1))
      ≤ 2 * (50 * ((k : ℝ) + 1)) ^ 2 * (4 * (50 * ((k : ℝ) + 1)) ^ 2)⁻¹ := by gcongr
    _ = 1 / 2 := by field_simp; ring

/-- Proof of `thm:memory`: if `k ≥ 2` and `0 < ε ≤ ε_k`, then `λ ≤ 1/(8 D₀²) ≤ 1/180000`. -/
theorem lam_le {k : ℕ} (hk : 2 ≤ k) {ε : ℝ} (h0 : 0 < ε) (hε : ε ≤ epsK k) :
    lam k ε ≤ 1 / 180000 := by
  have hQ : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hD : (150 : ℝ) ≤ 50 * ((k : ℝ) + 1) := by linarith
  have hB1 : (1 : ℝ) ≤ 4 * (50 * ((k : ℝ) + 1)) ^ 2 := by nlinarith
  have h := rpow_le_of_le_epsK h0 hε hQ
  have h2 : (4 * (50 * ((k : ℝ) + 1)) ^ 2) ^ (2 : ℝ) ≤
      (4 * (50 * ((k : ℝ) + 1)) ^ 2) ^ ((2 * ((k : ℝ) + 1) ^ 2 + 1) / ((k : ℝ) + 1) ^ 2) := by
    refine Real.rpow_le_rpow_of_exponent_le hB1 ?_
    rw [le_div_iff₀ hQ]
    linarith
  rw [Real.rpow_two] at h2
  have h3 : ε ^ (1 / ((k : ℝ) + 1) ^ 2) ≤ ((4 * (50 * ((k : ℝ) + 1)) ^ 2) ^ 2)⁻¹ :=
    h.trans (inv_anti₀ (by positivity) h2)
  unfold lam
  calc 2 * (50 * ((k : ℝ) + 1)) ^ 2 * ε ^ (1 / ((k : ℝ) + 1) ^ 2)
      ≤ 2 * (50 * ((k : ℝ) + 1)) ^ 2 * ((4 * (50 * ((k : ℝ) + 1)) ^ 2) ^ 2)⁻¹ := by gcongr
    _ = 1 / (8 * (50 * ((k : ℝ) + 1)) ^ 2) := by
        have : (50 * ((k : ℝ) + 1)) ≠ 0 := by positivity
        field_simp
        ring
    _ ≤ 1 / 180000 := by
        gcongr
        nlinarith

/-- Proof of `thm:memory`: `λ < 1`, and the bound `ε (1 + 2λ/(1 - λ))` is below `1.01 ε`. -/
theorem memoryBound_lt {k : ℕ} (hk : 2 ≤ k) {ε : ℝ} (h0 : 0 < ε) (hε : ε ≤ epsK k) :
    lam k ε < 1 ∧ ε * (1 + 2 * lam k ε / (1 - lam k ε)) < 1.01 * ε := by
  have hl := lam_le hk h0 hε
  have hl0 := lam_nonneg k h0.le
  refine ⟨by linarith, ?_⟩
  have hfrac : 2 * lam k ε / (1 - lam k ε) < 0.01 := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  nlinarith

end FNE

end
