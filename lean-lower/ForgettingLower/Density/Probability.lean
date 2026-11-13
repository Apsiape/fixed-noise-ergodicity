/- Exact finite-path density union bound, with the printed leading factor four.
Only deterministic encoding/terminal-set pairs are counted. -/
import ForgettingLower.Geometry.Noise
import ForgettingLower.Density.Witness

set_option autoImplicit false

noncomputable section

namespace FLD.Density

open FLD.Geometry MeasureTheory Classical
open FNE (box)
open scoped ENNReal

/-- The printed lower limit ceil(delta N / 12) for the number of distinct flags. -/
def minFlags (N : ℕ) : ℕ := ⌈delta * (N : ℝ) / 12⌉₊

/-- Some ordinary N-edge backward path from z is dense in marked-parent vertices.
The arbitrary continuation Q beyond N has no conditions and contributes no entropy. -/
def densePathEv (A : UND.CA 4) (z : Pt) (N : ℕ) : Set A.Noise₂ :=
  {ω | ∃ Q : ℕ → Pt, Q 0 = z ∧
    (∀ k < N, ∃ π, ∃ μ ∈ box 1, Q (k + 1) = par (Q k) π μ) ∧
    delta * (N : ℝ) ≤
      (((Finset.range N).filter (fun i => H (flagsOf ω) (Q i))).card : ℝ)}

theorem minFlags_le_card {N f : ℕ} (h : (N : ℝ) / 1404 ≤ 12 * (f : ℝ)) :
    minFlags N ≤ f := by
  apply Nat.ceil_le.mpr
  rw [Const.delta_eq]
  nlinarith

theorem minFlags_pos {N : ℕ} (hN : 1 ≤ N) : 1 ≤ minFlags N := by
  have h : 0 < delta * (N : ℝ) / 12 := by
    rw [Const.delta_eq]
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr h).ne'

/-- A dense finite path supplies a deterministic encoding with at least ceil(delta N/12)
distinct physical flags. The full path edge set is retained by the witness theorem. -/
theorem densePathEv_encoding (A : UND.CA 4) (z : Pt) (N : ℕ)
    {ω : A.Noise₂} (hω : ω ∈ densePathEv A z N) :
    ∃ Fl : Finset Pt, ∃ K : Finset (Sym2 Pt), minFlags N ≤ Fl.card ∧
      UND.Counting.IsEncoding nbr z (densityCost * Fl.card) K Fl ∧
      ∀ y ∈ Fl, flagsOf ω y.2 y.1 := by
  obtain ⟨Q, hQ, hstep, hdense⟩ := hω
  have hdense' : (N : ℝ) / 1404 ≤
      (((Finset.range N).filter (fun i => H (flagsOf ω) (Q i))).card : ℝ) := by
    simpa [Const.delta_eq, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdense
  obtain ⟨Fl, K, hmass, henc, _, hflags⟩ := exists_density_encoding hstep hdense'
  exact ⟨Fl, K, minFlags_le_card hmass, hQ ▸ henc, hflags⟩

/-- Theorem ld:density, exact finite-N probability bound. The leading four is
retained outside the sum; no random selection is assigned an independence premise. -/
theorem densePathEv_measure_le (A : UND.CA 4) {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1)
    (z : Pt) (N : ℕ) :
    A.noiseLaw₂ e (densePathEv A z N) ≤
      4 * ∑' j : ℕ, ((B : ℝ≥0∞) ^ densityCost * ENNReal.ofReal e) ^
        (j + minFlags N) := by
  classical
  let μ := A.noiseLaw₂ e
  let x := ENNReal.ofReal e
  let G := minFlags N
  let pairs := fun f => (UND.Counting.encLe nbr z (densityCost * f)).filter
    (fun p => p.2.card = f)
  let F : ℕ → Set A.Noise₂ := fun j => ⋃ p ∈ pairs (j + G),
    {ω | ∀ y ∈ p.2, flagsOf ω y.2 y.1}
  have hsub : densePathEv A z N ⊆ ⋃ j, F j := by
    intro ω hω
    obtain ⟨Fl, K, hG, henc, hflags⟩ := densePathEv_encoding A z N hω
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
      4 * ((B : ℝ≥0∞) ^ densityCost * x) ^ (j + G) := by
    intro j
    have hcard : (pairs (j + G)).card ≤ 4 * B ^ (densityCost * (j + G)) :=
      (Finset.card_filter_le _ _).trans
        (UND.Counting.card_encLe_le nbr Delta card_nbr_le
          (by norm_num [Delta, q, K]) z _)
    calc μ (F j) ≤ ((pairs (j + G)).card : ℝ≥0∞) * x ^ (j + G) := by
          apply UND.Counting.measure_biUnion_le_card_mul
          intro p hp
          have hc := (Finset.mem_filter.mp hp).2
          exact le_of_eq (by dsimp [μ, x]; rw [flags_measure A h0 h1, hc])
      _ ≤ ((4 * B ^ (densityCost * (j + G)) : ℕ) : ℝ≥0∞) * x ^ (j + G) := by
          gcongr
      _ = 4 * ((B : ℝ≥0∞) ^ densityCost * x) ^ (j + G) := by
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow, pow_mul,
            mul_assoc]
  calc μ (densePathEv A z N) ≤ μ (⋃ j, F j) := measure_mono hsub
    _ ≤ ∑' j, μ (F j) := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, 4 * ((B : ℝ≥0∞) ^ densityCost * x) ^ (j + G) :=
      ENNReal.tsum_le_tsum hF
    _ = 4 * ∑' j : ℕ, ((B : ℝ≥0∞) ^ densityCost * x) ^ (j + G) :=
      ENNReal.tsum_mul_left

end FLD.Density
