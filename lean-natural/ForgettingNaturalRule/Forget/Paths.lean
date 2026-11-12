/-
# Marked paths and marked roots at the natural threshold (Lemmas `nw:sparse`, `nw:paths`)
(nodes P1, M3)

Paper. Lemma `nw:paths`: "For a specified root and `N ≥ 1`, the probability of an ordinary backward
path of `N` edges all of whose vertices belong to `𝓜` is at most `Σ_{f ≥ ⌈N/50⌉} (4B^{101}ε)^f`.
Almost surely there is no infinite such path, simultaneously at every root." Lemma `nw:sparse`:
"`P(v ∈ 𝓜) ≤ ε(1 + 2λ/(1-λ)) < 2ε`."

The marked field `𝓜` of the natural rule is the noise-diagram core's raw marked set
`UND.Coh.marked` (same boxes, same Moore graph `Λ × S`, same closure rule), and its contour and
path lemmas are REUSED as they are: `UND.Raw.exists_contour` (Lemma `nw:arms`: `f` distinct flags,
`85e ≤ 4000(f-1)`), `UND.Raw.exists_cover` (the packing of Lemma `nw:paths`: `N ≤ 50f`, at most
`101f` edges), the encoding count `UND.Counting` (`nw:encoding`) through
`UND.Raw.measure_le_tsum_from`, and `UND.Raw.flags_measure` (`P(all flagged) = ε^f`). What is new
is the threshold: the noise-diagram core sums with base `K_mem ε` (its `Δ` is far larger); here the
base is `K_c ε = 4B^{101}ε ≤ 4B^{-99} ≤ 1/8` at the degree `Δ = 18q` of the ordinary graph
(`FNR.Const.Kc_mul_le`).

* **`pathEv_null_nat`**, **`raw_paths_nat`**: almost surely no infinite backward ordinary path in
  `𝓜`, simultaneously at every root (ADAPT `UND.Raw.pathEv_null`, `UND.Raw.raw_paths`);
* **`root_bound`**: `P(v ∈ 𝓜) ≤ Σ_{f ≥ 1} (K_c ε)^f ≤ 1/4` (weaker than the printed `< 2ε`,
  enough for the memory gap; `STATUS.md`, F2).
-/
import ForgettingNaturalRule.Constants
import UncomputableNoiseDiagram.Contour.RawPaths

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace FNR.Forget

open UND.Raw (Pt nbr card_nbr_le exists_contour exists_cover measure_le_tsum_from flags_measure
  PathEv OrdStep)
open UND.Coh (marked flagsOf)
open UND.Rule (ISite)
open FNE (box)

theorem Delta_pos : 1 ≤ Const.Delta := by rw [Const.Delta_eq]; norm_num

/-- `K_c ε ≤ 1/8` as an extended real. -/
theorem base_le {ε : ℝ} (hε : ε ≤ epsStar) :
    (Const.Kc : ℝ≥0∞) * ENNReal.ofReal ε ≤ 8⁻¹ := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  calc ENNReal.ofReal ((Const.Kc : ℝ) * ε) ≤ ENNReal.ofReal (1 / 8) :=
        ENNReal.ofReal_le_ofReal (Const.Kc_mul_le hε)
    _ = 8⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp

/-- The flag events of an encoding have probability at most `ε^g`. -/
theorem enc_le (A : UND.CA 6) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (g : ℕ) (Fl : Finset Pt) :
    A.noiseLaw₂ ε {ω | Fl.card = g ∧ ∀ y ∈ Fl, flagsOf ω y.2 y.1} ≤ ENNReal.ofReal ε ^ g := by
  by_cases hc : Fl.card = g
  · calc A.noiseLaw₂ ε {ω | Fl.card = g ∧ ∀ y ∈ Fl, flagsOf ω y.2 y.1}
        ≤ A.noiseLaw₂ ε {ω | ∀ y ∈ Fl, flagsOf ω y.2 y.1} :=
          measure_mono (fun ω (h : Fl.card = g ∧ ∀ y ∈ Fl, flagsOf ω y.2 y.1) => h.2)
      _ = ENNReal.ofReal ε ^ g := by rw [flags_measure A h0 h1, hc]
  · calc A.noiseLaw₂ ε {ω | Fl.card = g ∧ ∀ y ∈ Fl, flagsOf ω y.2 y.1}
        ≤ A.noiseLaw₂ ε ∅ :=
          measure_mono (fun ω (h : Fl.card = g ∧ ∀ y ∈ Fl, flagsOf ω y.2 y.1) => absurd h.1 hc)
      _ ≤ ENNReal.ofReal ε ^ g := by simp

/-- One root: the event of an infinite marked backward ordinary path has probability zero
(Lemma `nw:paths`, the tail `Σ_{f ≥ G} (K_c ε)^f → 0`). -/
theorem pathEv_null_nat (A : UND.CA 6) {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ epsStar) (w : ISite)
    (t : ℤ) : A.noiseLaw₂ ε (PathEv A w t) = 0 := by
  have h1 : ε ≤ 1 := hε.trans Const.epsStar_le_one
  set r : ℝ≥0∞ := (Const.Kc : ℝ≥0∞) * ENNReal.ofReal ε with hr
  have hr1 : r < 1 := (base_le hε).trans_lt (by norm_num)
  have hbound : ∀ G, 1 ≤ G → A.noiseLaw₂ ε (PathEv A w t) ≤ ∑' j : ℕ, r ^ (j + G) := by
    intro G hG
    refine measure_le_tsum_from (A.noiseLaw₂ ε) nbr Const.Delta 101 Const.Kc
      (fun a => card_nbr_le a) Delta_pos Const.four_le_Kc_pow ((w, t) : Pt) G hG
      (fun g _ Fl => {ω | Fl.card = g ∧ ∀ y ∈ Fl, flagsOf ω y.2 y.1}) (ENNReal.ofReal ε)
      (fun g _ K Fl _ => enc_le A h0 h1 g Fl) _ ?_
    intro ω hω
    obtain ⟨p, hp0, hstep, hmark⟩ := hω
    have hstepQ : ∀ k, ∃ π, ∃ μ ∈ box 1, ((p (k + 1), t - ((k + 1 : ℕ) : ℤ)) : Pt) =
        UND.Raw.par (p k, t - (k : ℤ)) π μ := by
      intro k
      obtain ⟨μ, hμ, π, he⟩ := hstep k
      refine ⟨π, μ, hμ, Prod.ext he ?_⟩
      show t - ((k + 1 : ℕ) : ℤ) = t - (k : ℤ) - 1
      push_cast; ring
    obtain ⟨Fl, K, h1', h2, h3, h4, h5, h6, -, h8⟩ :=
      exists_cover (E := flagsOf ω) (Q := fun k => (p k, t - (k : ℤ))) hstepQ
        (fun k => hmark k) (50 * G) 0
    have hQ0 : ((p 0, t - ((0 : ℕ) : ℤ)) : Pt) = (w, t) := by simp [hp0]
    rw [hQ0] at h4 h8
    exact ⟨Fl.card, by omega, K, Fl, ⟨h3, h5, h4, h8⟩, rfl, h6⟩
  have hsum : ∑' n : ℕ, r ^ n ≠ ⊤ := by
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hr1).ne'
  have ht := (ENNReal.tendsto_sum_nat_add (fun n => r ^ n) hsum).comp
    (Filter.tendsto_add_atTop_nat 1)
  exact le_zero_iff.mp (ge_of_tendsto' ht (fun i => hbound (i + 1) (by omega)))

/-- **Lemma `nw:paths`** (qualitative form): for `0 ≤ ε ≤ ε_*`, almost surely no infinite backward
ordinary dependency path lies in `𝓜`, simultaneously at every root. -/
theorem raw_paths_nat (A : UND.CA 6) {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ epsStar) :
    ∀ᵐ ω ∂(A.noiseLaw₂ ε), ∀ (t : ℤ) (p : ℕ → ISite), (∀ k, OrdStep (p k) (p (k + 1))) →
      ¬ ∀ k : ℕ, marked (flagsOf ω) (t - k) (p k) := by
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_)
    (measure_iUnion_null (fun z : ISite × ℤ => pathEv_null_nat A h0 hε z.1 z.2))
  simp only [Set.mem_ofPred_eq] at hω
  push Not at hω
  obtain ⟨t, p, hs, hm⟩ := hω
  exact Set.mem_iUnion.mpr ⟨(p 0, t), p, rfl, hs, hm⟩

/-- `Σ_{j ≥ 0} r^{j+1} ≤ 1/4` for `r ≤ 1/8`. -/
theorem tsum_pow_succ_le {r : ℝ≥0∞} (hr : r ≤ 8⁻¹) : ∑' j : ℕ, r ^ (j + 1) ≤ 4⁻¹ := by
  have h2 : r ≤ 2⁻¹ := hr.trans (ENNReal.inv_le_inv.2 (by norm_num))
  calc ∑' j : ℕ, r ^ (j + 1) ≤ ∑' j : ℕ, 8⁻¹ * (2⁻¹ : ℝ≥0∞) ^ j :=
        ENNReal.tsum_le_tsum fun j => by
          rw [pow_succ, mul_comm]
          gcongr
    _ = 8⁻¹ * 2 := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    _ = 4⁻¹ := by
        rw [show (8 : ℝ≥0∞) = 4 * 2 by norm_num,
          ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_assoc,
          ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

/-- **Sparse roots** (Lemma `nw:sparse`, weak form): for `0 ≤ ε ≤ ε_*`, a fixed space-time point is
marked with probability at most `Σ_{f ≥ 1} (K_c ε)^f ≤ 1/4`. -/
theorem root_bound (A : UND.CA 6) {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ epsStar) (w : ISite) (t : ℤ) :
    A.noiseLaw₂ ε {ω | marked (flagsOf ω) t w} ≤ 4⁻¹ := by
  have h1 : ε ≤ 1 := hε.trans Const.epsStar_le_one
  refine (measure_le_tsum_from (A.noiseLaw₂ ε) nbr Const.Delta 101 Const.Kc
    (fun a => card_nbr_le a) Delta_pos Const.four_le_Kc_pow ((w, t) : Pt) 1 le_rfl
    (fun g _ Fl => {ω | Fl.card = g ∧ ∀ y ∈ Fl, flagsOf ω y.2 y.1}) (ENNReal.ofReal ε)
    (fun g _ K Fl _ => enc_le A h0 h1 g Fl) _ ?_).trans (tsum_pow_succ_le (base_le hε))
  intro ω hω
  obtain ⟨e, Fl, K, h1', h2, h3, -, h5, h6, h7, h8⟩ :=
    exists_contour (E := flagsOf ω) (x := ((w, t) : Pt)) hω
  exact ⟨Fl.card, h1', K, Fl, ⟨by omega, h7, h5, h8⟩, rfl, h3⟩

end FNR.Forget
