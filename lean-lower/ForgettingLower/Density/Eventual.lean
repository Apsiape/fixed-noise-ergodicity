/- Summability and Borel-Cantelli for all paths, first at one root, then countably
many roots. The eventual horizon depends on the root and the innovations. -/
import ForgettingLower.Density.Probability
import ForgettingLower.Density.Rates
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

set_option autoImplicit false

noncomputable section

namespace FLD.Density

open FLD.Geometry MeasureTheory Classical Filter
open FNE (box)
open scoped ENNReal

/-- The ceiling in the exact tail dominates the integer block index N / 16848. -/
theorem div_le_minFlags (N : ℕ) : N / 16848 ≤ minFlags N := by
  have h := Nat.le_ceil (delta * (N : ℝ) / 12)
  change delta * (N : ℝ) / 12 ≤ (minFlags N : ℝ) at h
  rw [Const.delta_eq] at h
  have hN : N ≤ 16848 * minFlags N := by exact_mod_cast (by nlinarith :
    (N : ℝ) ≤ 16848 * (minFlags N : ℝ))
  omega

/-- Repeating each term of an ENNReal geometric series a fixed positive number
of times preserves finiteness. This counts all N, including N = 0. -/
theorem tsum_pow_div_ne_top {a : ℝ≥0∞} (ha : a < 1) :
    (∑' N : ℕ, a ^ (N / 16848)) ≠ ⊤ := by
  let idx : ℕ → Fin 16848 × ℕ := fun N =>
    (⟨N % 16848, Nat.mod_lt N (by norm_num)⟩, N / 16848)
  have hinj : Function.Injective idx := by
    intro m n h
    have hmod := congrArg (fun p : Fin 16848 × ℕ => p.1.val) h
    have hdiv := congrArg (fun p : Fin 16848 × ℕ => p.2) h
    dsimp [idx] at hmod hdiv
    omega
  have hgeo : (∑' n : ℕ, a ^ n) ≠ ⊤ := by
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (tsub_pos_of_lt ha).ne'
  have hprod : (∑' p : Fin 16848 × ℕ, a ^ p.2) ≠ ⊤ := by
    rw [ENNReal.tsum_prod']
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    exact ENNReal.mul_ne_top (by simp) hgeo
  exact ne_top_of_le_ne_top hprod
    (ENNReal.tsum_comp_le_tsum_of_injective hinj (fun p => a ^ p.2))

/-- The exact density tails are summable in N whenever their base is below one. -/
theorem tsum_density_tail_ne_top {a : ℝ≥0∞} (ha : a < 1) :
    (∑' N : ℕ, 4 * ∑' j : ℕ, a ^ (j + minFlags N)) ≠ ⊤ := by
  have hgeo : (∑' j : ℕ, a ^ j) ≠ ⊤ := by
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (tsub_pos_of_lt ha).ne'
  have hbound : ∀ N, 4 * ∑' j : ℕ, a ^ (j + minFlags N) ≤
      (4 * ∑' j : ℕ, a ^ j) * a ^ (N / 16848) := by
    intro N
    simp only [pow_add, ENNReal.tsum_mul_right]
    rw [mul_assoc]
    have hp := pow_le_pow_of_le_one (by positivity : 0 ≤ a) ha.le (div_le_minFlags N)
    exact mul_le_mul le_rfl (mul_le_mul le_rfl hp (by positivity) (by positivity))
      (by positivity) (by positivity)
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hbound)
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hgeo) (tsum_pow_div_ne_top ha)

/-- Exact finite-path bad-event probabilities are summable at the printed rate. -/
theorem tsum_densePathEv_ne_top (A : UND.CA 4) {e : ℝ} (h0 : 0 ≤ e)
    (he : e ≤ eps0) (z : Pt) :
    (∑' N : ℕ, A.noiseLaw₂ e (densePathEv A z N)) ≠ ⊤ := by
  let a : ℝ≥0∞ := (B : ℝ≥0∞) ^ densityCost * ENNReal.ofReal e
  have ha : a < 1 := by
    have heq : a = ENNReal.ofReal ((B : ℝ) ^ densityCost * e) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
      simp [a]
    rw [heq]
    apply ENNReal.ofReal_lt_one.mpr
    exact (Const.density_base_lt_quarter he).trans (by norm_num)
  exact ne_top_of_le_ne_top (tsum_density_tail_ne_top ha)
    (ENNReal.tsum_le_tsum (fun N => densePathEv_measure_le A h0
      (he.trans Const.eps0_le_one) z N))

/-- Almost surely at a fixed root all sufficiently long finite paths have
strictly fewer than delta N marked-parent vertices. -/
theorem eventually_sparse_at (A : UND.CA 4) {e : ℝ} (h0 : 0 ≤ e)
    (he : e ≤ eps0) (z : Pt) :
    ∀ᵐ ω ∂(A.noiseLaw₂ e), ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ Q : ℕ → Pt, Q 0 = z →
        (∀ k < N, ∃ π, ∃ μ ∈ box 1, Q (k + 1) = par (Q k) π μ) →
        (((Finset.range N).filter (fun i => H (flagsOf ω) (Q i))).card : ℝ) <
          delta * (N : ℝ) := by
  filter_upwards [ae_eventually_notMem (tsum_densePathEv_ne_top A h0 he z)] with ω hω
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hω
  refine ⟨N0, fun N hN Q hQ hstep => ?_⟩
  exact lt_of_not_ge (fun hdense => hN0 N hN ⟨Q, hQ, hstep, hdense⟩)

/-- Lemma ld:density: a probability-one event, simultaneous over every root,
with a separate finite cutoff for each root. -/
theorem all_path_density (A : UND.CA 4) {e : ℝ} (h0 : 0 ≤ e) (he : e ≤ eps0) :
    ∀ᵐ ω ∂(A.noiseLaw₂ e), ∀ z : Pt, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ Q : ℕ → Pt, Q 0 = z →
        (∀ k < N, ∃ π, ∃ μ ∈ box 1, Q (k + 1) = par (Q k) π μ) →
        (((Finset.range N).filter (fun i => H (flagsOf ω) (Q i))).card : ℝ) <
          delta * (N : ℝ) := by
  exact ae_all_iff.mpr (eventually_sparse_at A h0 he)

/-- On the same probability-one event no infinite ordinary backward path can
be entirely marked: every vertex of such a path would have a marked parent. -/
theorem no_infinite_marked_paths (A : UND.CA 4) {e : ℝ} (h0 : 0 ≤ e)
    (he : e ≤ eps0) :
    ∀ᵐ ω ∂(A.noiseLaw₂ e), ∀ Q : ℕ → Pt,
      (∀ k, ∃ π, ∃ μ ∈ box 1, Q (k + 1) = par (Q k) π μ) →
      ¬ ∀ k, marked (flagsOf ω) (Q k).2 (Q k).1 := by
  filter_upwards [all_path_density A h0 he] with ω hdensity
  intro Q hstep hmark
  have hH : ∀ k, H (flagsOf ω) (Q k) := by
    intro k
    obtain ⟨π, μ, hμ, hpar⟩ := hstep k
    refine ⟨μ, hμ, π, ?_⟩
    have hm := hmark (k + 1)
    rw [hpar] at hm
    exact hm
  obtain ⟨N0, hN0⟩ := hdensity (Q 0)
  let N := max N0 1
  have hbad := hN0 N (le_max_left _ _) Q rfl (fun k _ => hstep k)
  rw [Finset.filter_eq_self.mpr (fun k _ => hH k), Finset.card_range,
    Const.delta_eq] at hbad
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (le_max_right N0 1)
  nlinarith

/-- The no-infinite-marked-path conclusion in the product-site ordinary-step
coordinates used by the later complete-history argument. -/
theorem raw_paths (A : UND.CA 4) {e : ℝ} (h0 : 0 ≤ e) (he : e ≤ eps0) :
    ∀ᵐ ω ∂(A.noiseLaw₂ e), ∀ (t : ℤ) (p : ℕ → ISite),
      (∀ k, OrdStep (p k) (p (k + 1))) →
      ¬ ∀ k : ℕ, marked (flagsOf ω) (t - k) (p k) := by
  filter_upwards [no_infinite_marked_paths A h0 he] with ω hω
  intro t p hstep hmark
  apply hω (fun k => (p k, t - (k : ℤ))) _ hmark
  intro k
  obtain ⟨μ, hμ, π, hpar⟩ := hstep k
  refine ⟨π, μ, hμ, Prod.ext hpar ?_⟩
  change t - ((k + 1 : ℕ) : ℤ) = t - (k : ℤ) - 1
  push_cast
  ring

end FLD.Density
