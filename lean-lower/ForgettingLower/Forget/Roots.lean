/- Sparse physical roots from finite contours and deterministic encoding counts.
The weaker bound 1/4 suffices for two distinct invariant laws. -/
import ForgettingLower.Density.Probability
import ForgettingLower.Density.Rates

set_option autoImplicit false

noncomputable section
namespace FLD.Forget
open FLD.Geometry MeasureTheory Classical
open scoped ENNReal

/-- A marked physical root supplies a connected encoding with distinct flagged terminals. -/
theorem root_encoding (A : UND.CA 4) (cost : ℕ) (hcost : 12 ≤ cost) (z : Pt) {ω : A.Noise₂}
    (hω : marked (flagsOf ω) z.2 z.1) :
    ∃ Fl : Finset Pt, ∃ K : Finset (Sym2 Pt), 1 ≤ Fl.card ∧
      UND.Counting.IsEncoding nbr z (cost * Fl.card) K Fl ∧
      ∀ y ∈ Fl, flagsOf ω y.2 y.1 := by
  obtain ⟨e, Fl, K, hc⟩ := exists_contour hω
  have he := hc.edges_le
  obtain ⟨hpos, hcharge, hflag, hspan, hconn, hcard, hgraph, hverts, hbracket⟩ := hc
  refine ⟨Fl, K, hpos, ⟨?_, hgraph, hconn, hverts⟩, hflag⟩
  exact hcard.trans (he.trans (Nat.mul_le_mul hcost (Nat.sub_le _ _)))

/-- Union bound over fixed deterministic encodings; adaptive contours only supply witnesses. -/
theorem root_measure_le (A : UND.CA 4) (cost : ℕ) (hcost : 12 ≤ cost) {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) (z : Pt) :
    A.noiseLaw₂ e {ω | marked (flagsOf ω) z.2 z.1} ≤
      4 * ∑' j : ℕ, ((B : ℝ≥0∞) ^ cost * ENNReal.ofReal e) ^ (j + 1) := by
  classical
  let μ := A.noiseLaw₂ e
  let x := ENNReal.ofReal e
  let G : ℕ := 1
  let pairs := fun f => (UND.Counting.encLe nbr z (cost * f)).filter
    (fun p => p.2.card = f)
  let F : ℕ → Set A.Noise₂ := fun j => ⋃ p ∈ pairs (j + G),
    {ω | ∀ y ∈ p.2, flagsOf ω y.2 y.1}
  have hsub : {ω | marked (flagsOf ω) z.2 z.1} ⊆ ⋃ j, F j := by
    intro ω hω
    obtain ⟨Fl, K, hG, henc, hflags⟩ := root_encoding A cost hcost z hω
    let j := Fl.card - G
    have hj : j + G = Fl.card := by dsimp [j, G]; omega
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    dsimp [F]
    refine Set.mem_iUnion.mpr ⟨(K, Fl), Set.mem_iUnion.mpr ⟨?_, hflags⟩⟩
    dsimp [pairs]
    rw [hj]
    exact Finset.mem_filter.mpr
      ⟨UND.Counting.mem_encLe nbr Delta card_nbr_le henc, rfl⟩
  have hF : ∀ j, μ (F j) ≤
      4 * ((B : ℝ≥0∞) ^ cost * x) ^ (j + G) := by
    intro j
    have hcard : (pairs (j + G)).card ≤ 4 * B ^ (cost * (j + G)) :=
      (Finset.card_filter_le _ _).trans
        (UND.Counting.card_encLe_le nbr Delta card_nbr_le
          (by norm_num [Delta, q, K]) z _)
    calc μ (F j) ≤ ((pairs (j + G)).card : ℝ≥0∞) * x ^ (j + G) := by
          apply UND.Counting.measure_biUnion_le_card_mul
          intro p hp
          have hc : p.2.card = j + G := (Finset.mem_filter.mp hp).2
          exact le_of_eq (by dsimp [μ, x]; rw [flags_measure A h0 h1, hc])
      _ ≤ ((4 * B ^ (cost * (j + G)) : ℕ) : ℝ≥0∞) * x ^ (j + G) := by
          gcongr
      _ = 4 * ((B : ℝ≥0∞) ^ cost * x) ^ (j + G) := by
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow, pow_mul,
            mul_assoc]
  calc μ ({ω | marked (flagsOf ω) z.2 z.1}) ≤ μ (⋃ j, F j) := measure_mono hsub
    _ ≤ ∑' j, μ (F j) := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, 4 * ((B : ℝ≥0∞) ^ cost * x) ^ (j + G) :=
      ENNReal.tsum_le_tsum hF
    _ = 4 * ∑' j : ℕ, ((B : ℝ≥0∞) ^ cost * x) ^ (j + G) :=
      ENNReal.tsum_mul_left


/-- The exact allowed rate leaves enough entropy slack for the root gap. -/
theorem root_base_le {e : ℝ} (he : e ≤ eps0) :
    (B : ℝ≥0∞) ^ densityCost * ENNReal.ofReal e ≤ 32⁻¹ := by
  have hb : (32 : ℝ) ≤ B := by rw [Const.B_eq]; norm_num
  have ht : (B : ℝ) ≤ (B : ℝ) ^ densityCost := by
    simpa using (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ B)
      (by norm_num [densityCost] : 1 ≤ densityCost))
  have hi : ((B : ℝ) ^ densityCost)⁻¹ ≤ 1 / 32 := by
    rw [one_div]
    exact (inv_le_inv₀ (by linarith : (0 : ℝ) < (B : ℝ) ^ densityCost) (by norm_num : (0 : ℝ) < 32)).mpr (hb.trans ht)
  have hr := (Const.density_base_le he).trans hi
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal ((B : ℝ) ^ densityCost * e) ≤ ENNReal.ofReal (1 / 32) :=
      ENNReal.ofReal_le_ofReal hr
    _ = 32⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp

/-- Sum all positive terminal counts, including the leading factor four. -/
theorem root_tail_le {r : ℝ≥0∞} (hr : r ≤ 32⁻¹) :
    4 * ∑' j : ℕ, r ^ (j + 1) ≤ 4⁻¹ := by
  have h2 : r ≤ 2⁻¹ := hr.trans (ENNReal.inv_le_inv.2 (by norm_num))
  calc 4 * ∑' j : ℕ, r ^ (j + 1) ≤
      4 * ∑' j : ℕ, 32⁻¹ * (2⁻¹ : ℝ≥0∞) ^ j := by
        apply mul_le_mul_right
        apply ENNReal.tsum_le_tsum
        intro j
        rw [pow_succ, mul_comm]
        exact mul_le_mul' hr (pow_le_pow_left' h2 j)
    _ = 4 * (32⁻¹ * 2) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    _ = 4⁻¹ := by
      have h32 : (32 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 32) := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
      have h4 : (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 4) := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
      rw [h32, h4]
      calc (4 : ℝ≥0∞) * (ENNReal.ofReal (1 / 32) * 2) =
          ENNReal.ofReal (4 * ((1 / 32 : ℝ) * 2)) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
            norm_num
        _ = ENNReal.ofReal (1 / 4) := by norm_num

/-- Sparse roots at every fixed physical vertex, independently of the Wang alphabet. -/
theorem root_bound (A : UND.CA 4) {e : ℝ} (h0 : 0 ≤ e) (he : e ≤ eps0)
    (w : ISite) (t : ℤ) : A.noiseLaw₂ e {ω | marked (flagsOf ω) t w} ≤ 4⁻¹ :=
  (root_measure_le A densityCost (by norm_num [densityCost]) h0 (he.trans Const.eps0_le_one) (w, t)).trans
    (root_tail_le (root_base_le he))

end FLD.Forget
