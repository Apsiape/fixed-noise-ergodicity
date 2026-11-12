/-
# The effective constants (`nw:constants`) (node A3)

Paper (Section 2.3, (`nw:constants`)): "`Δ = 18q`, `B = 2Δ²`, `ε_* = B^{-200}`, `κ = 4B^{-99}`.
These are effective constants independent of `R`. Indeed `q = 5·2^16`, `Δ = 90·2^16` and
`B = 16200·2^32 > 2^45`. In particular `κ < 1`." Lemma `nw:paths`: "At the stipulated rate the
base obeys `4B^{101}ε ≤ 4B^{-99} = κ < 1`."

* `Delta`, `B`, `Kc = 4B^{101}` (the witness-count base of the path tail), `B_eq`,
  `epsStar_eq` (`ε_* = B^{-200}`), `epsStar_pos`, `epsStar_le_one`;
* `four_le_Kc_pow`: `4(2Δ²)^{101g} ≤ K_c^g` for `g ≥ 1` (the count of `≤ 101g`-edge encodings,
  Lemma 9.1 of the noise-diagram paper, at degree `Δ = 18q`);
* `Kc_mul_le`: `K_c ε ≤ 4B^{-99} ≤ 1/8` for `ε ≤ ε_*`.
-/
import ForgettingNaturalRule.Statements
import UncomputableNoiseDiagram.Parameters.Geometry

set_option autoImplicit false

noncomputable section

namespace FNR.Const

/-- (`nw:constants`): `Δ = 18q`, the undirected degree of the ordinary graph. -/
def Delta : ℕ := 18 * UND.Param.q

/-- (`nw:constants`): `B = 2Δ²`. -/
def B : ℕ := 2 * Delta ^ 2

/-- The witness-count base `K_c = 4B^{101}` of the path tail (`nw:pathtail`). -/
def Kc : ℕ := 4 * B ^ 101

/-- (`nw:constants`): `Δ = 90·2^16`. -/
theorem Delta_eq : Delta = 90 * 2 ^ 16 := by norm_num [Delta, UND.Param.q, UND.Param.K]

/-- (`nw:constants`): `B = 16200·2^32`. -/
theorem B_eq : B = 16200 * 2 ^ 32 := by norm_num [B, Delta_eq]

theorem B_ge : 32 ≤ B := by rw [B_eq]; norm_num

/-- `ε_* = B^{-200}`. -/
theorem epsStar_eq : epsStar = ((B : ℝ) ^ 200)⁻¹ := by
  unfold epsStar B Delta UND.Param.q UND.Param.K
  rfl

theorem epsStar_pos : 0 < epsStar := by
  rw [epsStar_eq]
  have : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le (by norm_num) B_ge)
  positivity

theorem epsStar_le_one : epsStar ≤ 1 := by
  rw [epsStar_eq]
  have hB : (1 : ℝ) ≤ B := by exact_mod_cast (le_trans (by norm_num) B_ge)
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hB)

/-- The encoding count at degree `Δ`: `4(2Δ²)^{101g} ≤ K_c^g` for `g ≥ 1`. -/
theorem four_le_Kc_pow (g : ℕ) (hg : 1 ≤ g) : 4 * (2 * Delta ^ 2) ^ (101 * g) ≤ Kc ^ g := by
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  change 4 * B ^ (101 * (g + 1)) ≤ (4 * B ^ 101) ^ (g + 1)
  rw [mul_pow, ← pow_mul, mul_comm 101 (g + 1)]
  exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) 4)

/-- A real inequality for every base `b ≥ 32`: `4b^{101}·b^{-200} ≤ 1/8`. -/
theorem four_mul_pow_le (b : ℝ) (hb : 32 ≤ b) : 4 * b ^ 101 * (b ^ 200)⁻¹ ≤ 1 / 8 := by
  have hb0 : 0 < b := by linarith
  have h200 : b ^ 200 = b ^ 101 * b ^ 99 := by rw [← pow_add]
  rw [h200, mul_inv, ← mul_assoc, mul_assoc 4, mul_inv_cancel₀ (pow_pos hb0 _).ne', mul_one]
  have h99 : b ≤ b ^ 99 := le_self_pow₀ (by linarith) (by norm_num)
  have : 32 ≤ b ^ 99 := le_trans hb h99
  rw [div_eq_mul_inv, ← div_eq_mul_inv, ← div_eq_mul_inv]
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- **The path-tail base** (Lemma `nw:paths`): `K_c ε ≤ 4B^{-99} ≤ 1/8` for `ε ≤ ε_*`. -/
theorem Kc_mul_le {ε : ℝ} (hε : ε ≤ epsStar) : (Kc : ℝ) * ε ≤ 1 / 8 := by
  have hb : (32 : ℝ) ≤ B := by exact_mod_cast B_ge
  have hK : (Kc : ℝ) = 4 * (B : ℝ) ^ 101 := by unfold Kc; push_cast; ring
  calc (Kc : ℝ) * ε ≤ (Kc : ℝ) * epsStar := mul_le_mul_of_nonneg_left hε (by positivity)
    _ = 4 * (B : ℝ) ^ 101 * ((B : ℝ) ^ 200)⁻¹ := by rw [hK, epsStar_eq]
    _ ≤ 1 / 8 := four_mul_pow_le _ hb

end FNR.Const
