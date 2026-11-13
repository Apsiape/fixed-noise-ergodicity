/-
# The Peierls sum (Sections 3.6 and 4.4)

Both `mem:field-bound` and `thm:forgetting` end with the same union bound: an event of the noise
forces, for some `e ≥ e₀`, a connected set `K` of `e` edges of `𝒢` at a fixed vertex `θ₀` and a
set `Σ` of replacement events among the vertices of `K` with `|Σ| ≥ c + r e`. There are at most
`D₀^{2e}` such `K` (`fgt:count`), at most `2^{e+1}` such `Σ` for each `K` (a connected `e`-edge
set has at most `e + 1` vertices), and each `Σ` has probability `ε^{|Σ|} ≤ ε^{c + r e}`. Hence the
probability is at most `Σ_{e ≥ e₀} D₀^{2e} 2^{e+1} ε^{c + r e} = 2 ε^c β^{e₀} / (1 - β)` with
`β = 2 D₀² ε^r < 1`. This file proves that bound once (`peierls`); the two sections specialize it
(`c = 1`, `r = 1/q²`, `e₀ = 1` for the memory field; `c = -τ/a`, `r = 1/a`, `e₀ = t` for
forgetting).
-/
import FixedNoiseErgodicity.Section3.Contour
import FixedNoiseErgodicity.Section2.Process
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section

namespace FNE

open MeasureTheory
open scoped ENNReal

variable {k : ℕ} {R : WangSet}

/-! ## Events on a finite set of space-time points -/

/-- The event "every point of `Σ` is a replacement event". -/
def allEvents (Sig : Finset (STPoint k)) : Set (Noise k R) :=
  {ω | ∀ φ ∈ Sig, φ ∈ eventSet ω.flags}

/-- `P(every point of Σ is an event) ≤ ε^{|Σ|}`: events occur only at positive times,
independently with probability `ε` (an equality when all points of `Σ` have positive time). -/
theorem noiseLaw_allEvents_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (Sig : Finset (STPoint k)) :
    noiseLaw k R ε (allEvents Sig) ≤ ENNReal.ofReal ε ^ Sig.card := by
  classical
  by_cases hz : ∃ φ ∈ Sig, φ.2 = 0
  · obtain ⟨φ, hφ, h⟩ := hz
    have : allEvents (R := R) Sig = ∅ := by
      ext ω
      simp only [allEvents, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hall
      obtain ⟨t, ht, -⟩ := hall φ hφ
      omega
    rw [this, measure_empty]
    exact bot_le
  · push Not at hz
    let f : STPoint k → ℕ × Site k := fun θ => (θ.2 - 1, θ.1)
    have hinj : Set.InjOn f Sig := by
      intro a ha b hb hab
      have h1 := hz a ha
      have h2 := hz b hb
      simp only [f, Prod.mk.injEq] at hab
      exact Prod.ext hab.2 (by omega)
    have hsub : allEvents (R := R) Sig ⊆ {ω | ∀ p ∈ Sig.image f, (ω p).1 = true} := by
      intro ω hω p hp
      obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨t, ht, hη⟩ := hω φ hφ
      simp only [f, ht, Nat.add_sub_cancel]
      exact hη
    calc noiseLaw k R ε (allEvents Sig)
        ≤ noiseLaw k R ε {ω | ∀ p ∈ Sig.image f, (ω p).1 = true} := measure_mono hsub
      _ = ENNReal.ofReal ε ^ (Sig.image f).card := noiseLaw_flags_eq h0 h1 _
      _ = ENNReal.ofReal ε ^ Sig.card := by rw [Finset.card_image_of_injOn hinj]

/-! ## The vertices of a connected edge set -/

open Classical in
/-- A finite set of at most `|K| + 1` vertices containing `θ₀` and both ends of every edge of `K`,
when `K` is connected at `θ₀` (`EdgeCount.exists_vertices`); `∅` otherwise. -/
def vertsOf (θ₀ : STPoint k) (K : Finset (Sym2 (STPoint k))) : Finset (STPoint k) :=
  if h : EdgeCount.ConnectedAt K θ₀ then (EdgeCount.exists_vertices h).choose else ∅

theorem vertsOf_spec {θ₀ : STPoint k} {K : Finset (Sym2 (STPoint k))}
    (h : EdgeCount.ConnectedAt K θ₀) :
    (vertsOf θ₀ K).card ≤ K.card + 1 ∧ θ₀ ∈ vertsOf θ₀ K ∧
      ∀ e ∈ K, ∀ v ∈ e, v ∈ vertsOf θ₀ K := by
  rw [vertsOf, dif_pos h]
  exact (EdgeCount.exists_vertices h).choose_spec

/-! ## The Peierls bound -/

/-- A *Peierls witness* of size `e` at `θ₀` with exponent bound `g` for the noise `ω`: a set `K`
of `e` edges of `𝒢`, connected at `θ₀`, and a set `Σ` of replacement events of `ω`, each equal to
`θ₀` or an end of an edge of `K`, with `g ≤ |Σ|`. -/
def PeierlsWitness (θ₀ : STPoint k) (g : ℝ) (e : ℕ) (ω : Noise k R) : Prop :=
  ∃ K : Finset (Sym2 (STPoint k)), K.card = e ∧ (∀ x ∈ K, IsGEdge x) ∧
    EdgeCount.ConnectedAt K θ₀ ∧ ∃ Sig : Finset (STPoint k),
      (∀ φ ∈ Sig, φ = θ₀ ∨ ∃ x ∈ K, φ ∈ x) ∧ g ≤ Sig.card ∧ ∀ φ ∈ Sig, φ ∈ eventSet ω.flags

/-- One term of the Peierls sum: `P(some witness of size e) ≤ D₀^{2e} 2^{e+1} ε^g`. -/
theorem noiseLaw_witness_le {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) (θ₀ : STPoint k) (g : ℝ)
    (e : ℕ) :
    noiseLaw k R ε {ω | PeierlsWitness θ₀ g e ω} ≤
      ENNReal.ofReal ((50 * ((k : ℝ) + 1)) ^ (2 * e) * 2 ^ (e + 1) * ε ^ g) := by
  classical
  obtain ⟨hfin, hncard⟩ := finite_connected (k := k) θ₀ e
  set 𝒦 := hfin.toFinset with h𝒦
  set T : Finset (Sym2 (STPoint k)) → Finset (Finset (STPoint k)) :=
    fun K => (vertsOf θ₀ K).powerset.filter (fun S => g ≤ (S.card : ℝ)) with hT
  have hsub : {ω : Noise k R | PeierlsWitness θ₀ g e ω} ⊆
      ⋃ K ∈ 𝒦, ⋃ S ∈ T K, allEvents (R := R) S := by
    rintro ω ⟨K, hcard, hG, hconn, Sig, hSig, hg, hev⟩
    simp only [Set.mem_iUnion]
    obtain ⟨-, hz, hall⟩ := vertsOf_spec hconn
    refine ⟨K, (Set.Finite.mem_toFinset _).mpr ⟨hcard, hG, hconn⟩, Sig,
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hg⟩, hev⟩
    intro φ hφ
    rcases hSig φ hφ with rfl | ⟨x, hx, hφx⟩
    · exact hz
    · exact hall x hx φ hφx
  have hS : ∀ K ∈ 𝒦, ∀ S ∈ T K, noiseLaw k R ε (allEvents S) ≤ ENNReal.ofReal (ε ^ g) := by
    intro K _ S hS
    have hg : g ≤ (S.card : ℝ) := (Finset.mem_filter.mp hS).2
    refine (noiseLaw_allEvents_le h0.le h1 S).trans ?_
    rw [← ENNReal.ofReal_pow h0.le, ← Real.rpow_natCast]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge h0 h1 hg)
  have hTcard : ∀ K ∈ 𝒦, (T K).card ≤ 2 ^ (e + 1) := by
    intro K hK
    obtain ⟨hcard, -, hconn⟩ := (Set.Finite.mem_toFinset _).mp hK
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_powerset]
    exact Nat.pow_le_pow_right (by norm_num) (hcard ▸ (vertsOf_spec hconn).1)
  have h𝒦card : 𝒦.card ≤ (50 * (k + 1)) ^ (2 * e) := by
    rw [h𝒦, ← Set.ncard_eq_toFinset_card _ hfin]
    exact hncard
  calc noiseLaw k R ε {ω | PeierlsWitness θ₀ g e ω}
      ≤ noiseLaw k R ε (⋃ K ∈ 𝒦, ⋃ S ∈ T K, allEvents (R := R) S) := measure_mono hsub
    _ ≤ ∑ K ∈ 𝒦, noiseLaw k R ε (⋃ S ∈ T K, allEvents (R := R) S) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ K ∈ 𝒦, ∑ S ∈ T K, noiseLaw k R ε (allEvents (R := R) S) :=
        Finset.sum_le_sum (fun K _ => measure_biUnion_finset_le _ _)
    _ ≤ ∑ K ∈ 𝒦, ∑ S ∈ T K, ENNReal.ofReal (ε ^ g) :=
        Finset.sum_le_sum (fun K hK => Finset.sum_le_sum (fun S hS' => hS K hK S hS'))
    _ ≤ ∑ K ∈ 𝒦, ((2 ^ (e + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (ε ^ g) := by
        refine Finset.sum_le_sum (fun K hK => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact hTcard K hK
    _ = (𝒦.card : ℝ≥0∞) * (((2 ^ (e + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (ε ^ g)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((50 * (k + 1)) ^ (2 * e) : ℕ) : ℝ≥0∞) *
          (((2 ^ (e + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (ε ^ g)) := by
        gcongr
    _ = ENNReal.ofReal ((50 * ((k : ℝ) + 1)) ^ (2 * e) * 2 ^ (e + 1) * ε ^ g) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]
        congr 1
        · rw [← ENNReal.ofReal_natCast]
          push_cast
          rfl
        · congr 1
          rw [← ENNReal.ofReal_natCast]
          push_cast
          rfl

/-- The terms of the Peierls sum: `D^{2e} 2^{e+1} ε^{c + r e} = 2 ε^c (2 D² ε^r)^e`. -/
theorem peierls_term {ε : ℝ} (h0 : 0 < ε) (D c r : ℝ) (e : ℕ) :
    D ^ (2 * e) * 2 ^ (e + 1) * ε ^ (c + r * (e : ℝ)) = 2 * ε ^ c * (2 * D ^ 2 * ε ^ r) ^ e := by
  rw [Real.rpow_add h0, Real.rpow_mul h0.le, Real.rpow_natCast]
  ring

/-- **The Peierls sum** (end of the proofs of `mem:field-bound` and `thm:forgetting`). Let
`0 < ε ≤ 1`, `c, r ∈ ℝ` and `β = 2 D₀² ε^r < 1`, `D₀ = 50q`. If every noise in `A` has, for some
`e ≥ e₀`, a Peierls witness of size `e` at `θ₀` with `|Σ| ≥ c + r e`, then
`P(A) ≤ Σ_{e ≥ e₀} D₀^{2e} 2^{e+1} ε^{c + r e} = 2 ε^c β^{e₀} / (1 - β)`. -/
theorem peierls {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) (c r : ℝ)
    (hβ : 2 * (50 * ((k : ℝ) + 1)) ^ 2 * ε ^ r < 1) (θ₀ : STPoint k) (e₀ : ℕ)
    (A : Set (Noise k R)) (hA : ∀ ω ∈ A, ∃ e, e₀ ≤ e ∧ PeierlsWitness θ₀ (c + r * e) e ω) :
    noiseLaw k R ε A ≤
      ENNReal.ofReal (2 * ε ^ c * (2 * (50 * ((k : ℝ) + 1)) ^ 2 * ε ^ r) ^ e₀ /
        (1 - 2 * (50 * ((k : ℝ) + 1)) ^ 2 * ε ^ r)) := by
  set β : ℝ := 2 * (50 * ((k : ℝ) + 1)) ^ 2 * ε ^ r with hβdef
  have hβ0 : 0 ≤ β := by positivity
  have hterm : ∀ e : ℕ, (50 * ((k : ℝ) + 1)) ^ (2 * e) * 2 ^ (e + 1) * ε ^ (c + r * (e : ℝ)) =
      2 * ε ^ c * β ^ e := fun e => by rw [hβdef]; exact peierls_term h0 _ c r e
  have hsub : A ⊆ ⋃ n : ℕ, {ω | PeierlsWitness θ₀ (c + r * ((n + e₀ : ℕ) : ℝ)) (n + e₀) ω} := by
    intro ω hω
    obtain ⟨e, he, hw⟩ := hA ω hω
    refine Set.mem_iUnion.mpr ⟨e - e₀, ?_⟩
    rw [Nat.sub_add_cancel he]
    exact hw
  have hsum : Summable (fun n : ℕ => (2 * ε ^ c * β ^ e₀) * β ^ n) :=
    (summable_geometric_of_lt_one hβ0 hβ).mul_left _
  calc noiseLaw k R ε A
      ≤ ∑' n : ℕ, noiseLaw k R ε
          {ω | PeierlsWitness θ₀ (c + r * ((n + e₀ : ℕ) : ℝ)) (n + e₀) ω} :=
        (measure_mono hsub).trans (measure_iUnion_le _)
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((2 * ε ^ c * β ^ e₀) * β ^ n) := by
        refine ENNReal.tsum_le_tsum (fun n => ?_)
        refine (noiseLaw_witness_le h0 h1 θ₀ _ _).trans_eq ?_
        rw [hterm, pow_add]
        ring_nf
    _ = ENNReal.ofReal (∑' n : ℕ, (2 * ε ^ c * β ^ e₀) * β ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum).symm
    _ = ENNReal.ofReal (2 * ε ^ c * β ^ e₀ / (1 - β)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ, div_eq_mul_inv]

end FNE

end
