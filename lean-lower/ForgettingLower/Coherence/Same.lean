/- Amortized same-site coherence on the all-path density event.
The two path cutoffs are chosen separately at their actual starting roots. -/
import ForgettingLower.Coherence.Providers
import ForgettingLower.Coherence.Pairing
import ForgettingLower.Density.Eventual

set_option autoImplicit false

noncomputable section
namespace FLD.Coh

open FLD.Geometry FLD.Rule
open FNE (Plane WangSet box)
open Classical MeasureTheory

variable {R : WangSet} {X : ℤ → ISite → Option R} {E : ℤ → ISite → Prop}

/-- The deterministic, simultaneous-every-root conclusion of the density lemma. -/
def DensityEvent (E : ℤ → ISite → Prop) : Prop :=
  ∀ z : Pt, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ Q : ℕ → Pt, Q 0 = z →
    (∀ k < N, ∃ π, ∃ μ ∈ box 1, Q (k + 1) = par (Q k) π μ) →
    (((Finset.range N).filter (fun i => H E (Q i))).card : ℝ) < delta * (N : ℝ)

/-- Different live labels at the same planar site force different transverse positions. -/
theorem transverse_ne {t : ℤ} {u : Plane} {P Q : Fin 2 → ℤ} {a b : R}
    (hab : a ≠ b) (h : UL X (marked E) t (u, P) a)
    (h' : UL X (marked E) t (u, Q) b) : P ≠ Q := by
  rintro rfl
  exact hab (Option.some_injective _ (h.2.symm.trans h'.2))

/-- One paired ancestry step: a non-H step contracts by one; an H step costs at most D. -/
theorem paired_step (hX : IsHistory X E) {t : ℤ} {u : Plane} {P Q : Fin 2 → ℤ}
    {a b : R} (hab : a ≠ b) (h : UL X (marked E) t (u, P) a)
    (h' : UL X (marked E) t (u, Q) b) :
    ∃ π π' : Provider,
      UL X (marked E) (t - 1) (u, P + offset π) a ∧
      UL X (marked E) (t - 1) (u, Q + offset π') b ∧
      sep (P + offset π) (Q + offset π') + 1 ≤
        sep P Q + (D + 1) * (if H E ((u, P), t) ∨ H E ((u, Q), t) then 1 else 0) := by
  classical
  by_cases hH : H E ((u, P), t) ∨ H E ((u, Q), t)
  · obtain ⟨π, hc, hm⟩ := exists_good hX h
    obtain ⟨π', hc', hm'⟩ := exists_good hX h'
    refine ⟨π, π', ul_of_good hc hm, ul_of_good hc' hm', ?_⟩
    simp only [ite_eq_left hH, mul_one]
    have := sep_add_le P Q π π'
    omega
  · have hH1 : ¬ H E ((u, P), t) := fun hh => hH (Or.inl hh)
    have hH2 : ¬ H E ((u, Q), t) := fun hh => hH (Or.inr hh)
    have hf1 := card_failed_le (h.gi (hX.isTraj (t - 1)) (marked_closed E) (by omega))
    have hf2 := card_failed_le (h'.gi (hX.isTraj (t - 1)) (marked_closed E) (by omega))
    let Bad1 : Finset Provider := Finset.univ.filter fun π =>
      ¬ chkI (fun v => X (t - 1) (v, P + offset π)) u = some a
    let Bad2 : Finset Provider := Finset.univ.filter fun π =>
      ¬ chkI (fun v => X (t - 1) (v, Q + offset π)) u = some b
    have hcard : Bad1.card + Bad2.card < 3 * 15 * 16 := by
      change Bad1.card ≤ K at hf1
      change Bad2.card ≤ K at hf2
      rw [Const.K_eq] at hf1 hf2
      omega
    have good1 : ∀ π, π ∉ Bad1 → UL X (marked E) (t - 1) (u, P + offset π) a := by
      intro π hπ
      have hc : chkI (fun v => X (t - 1) (v, P + offset π)) u = some a := by
        simpa [Bad1] using hπ
      exact ul_of_good hc (clean_of_not_H hH1 π)
    have good2 : ∀ π, π ∉ Bad2 → UL X (marked E) (t - 1) (u, Q + offset π) b := by
      intro π hπ
      have hc : chkI (fun v => X (t - 1) (v, Q + offset π)) u = some b := by
        simpa [Bad2] using hπ
      exact ul_of_good hc (clean_of_not_H hH2 π)
    obtain ⟨j, hj⟩ : ∃ j, P j ≠ Q j := by
      by_contra hc
      push Not at hc
      exact transverse_ne hab h h' (funext hc)
    simp only [ite_eq_right hH, mul_zero, add_zero]
    by_cases hdir : P j < Q j
    · obtain ⟨s, hs1, hs2⟩ := exists_pair (pHi j) (pLo j) (pHi_injective j)
        (pLo_injective j) Bad1 Bad2 hcard
      refine ⟨pHi j s, pLo j s, good1 _ hs1, good2 _ hs2, ?_⟩
      exact (sep_step (offset (pHi j s)) (offset (pLo j s)) (fun i => by
        rw [offset_pair j s i, Int.sign_eq_one_of_pos (by omega)]
        split_ifs <;> ring) hj).le
    · obtain ⟨s, hs1, hs2⟩ := exists_pair (pLo j) (pHi j) (pLo_injective j)
        (pHi_injective j) Bad1 Bad2 hcard
      refine ⟨pLo j s, pHi j s, good1 _ hs1, good2 _ hs2, ?_⟩
      exact (sep_step (offset (pLo j s)) (offset (pHi j s)) (fun i => by
        rw [offset_pair j s i, Int.sign_eq_neg_one_of_neg (by omega)]
        split_ifs <;> ring) hj).le

/-- Summing the one-step inequalities pays D+1 for each bad paired step. -/
theorem distance_drift (d : ℕ → ℕ) (bad : ℕ → Prop)
    (hstep : ∀ k, d (k + 1) + 1 ≤ d k + (D + 1) * (if bad k then 1 else 0)) (N : ℕ) :
    d N + N ≤ d 0 + (D + 1) * ((Finset.range N).filter bad).card := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
    have hs := hstep N
    have hn : N ∉ (Finset.range N).filter bad := fun hn =>
      (Nat.lt_irrefl N) (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)
    by_cases hb : bad N
    · rw [Finset.range_add_one, Finset.filter_insert, ite_eq_left hb, Finset.card_insert_of_notMem hn]
      simp only [ite_eq_left hb, mul_one] at hs
      simp only [D] at ih hs ⊢
      omega
    · rw [Finset.range_add_one, Finset.filter_insert, ite_eq_right hb]
      simp only [ite_eq_right hb, mul_zero, add_zero] at hs
      omega

/-- Lemma ld:z4coherence: every complete flag history is coherent at one planar site and time. -/
theorem same_site (hX : IsHistory X E) (hden : DensityEvent E)
    {t : ℤ} {u : Plane} {P Q : Fin 2 → ℤ} {a b : R}
    (h : UL X (marked E) t (u, P) a) (h' : UL X (marked E) t (u, Q) b) : a = b := by
  classical
  by_contra hab
  let State := {z : ℤ × ((Fin 2 → ℤ) × (Fin 2 → ℤ)) //
    UL X (marked E) z.1 (u, z.2.1) a ∧ UL X (marked E) z.1 (u, z.2.2) b}
  let z0 : State := ⟨(t, P, Q), h, h'⟩
  have hex : ∀ z : State, ∃ z' : State, z'.1.1 = z.1.1 - 1 ∧
      (∃ π π', z'.1.2.1 = z.1.2.1 + offset π ∧ z'.1.2.2 = z.1.2.2 + offset π') ∧
      sep z'.1.2.1 z'.1.2.2 + 1 ≤ sep z.1.2.1 z.1.2.2 + (D + 1) *
        (if H E ((u, z.1.2.1), z.1.1) ∨ H E ((u, z.1.2.2), z.1.1) then 1 else 0) := by
    intro z
    obtain ⟨π, π', h1, h2, hd⟩ := paired_step hX hab z.2.1 z.2.2
    exact ⟨⟨(z.1.1 - 1, z.1.2.1 + offset π, z.1.2.2 + offset π'), h1, h2⟩,
      rfl, ⟨π, π', rfl, rfl⟩, hd⟩
  choose f hf using hex
  let Z : ℕ → State := fun n => f^[n] z0
  have hZ (n : ℕ) : Z (n + 1) = f (Z n) := by simp [Z, Function.iterate_succ_apply']
  let Q1 : ℕ → Pt := fun n => ((u, (Z n).1.2.1), (Z n).1.1)
  let Q2 : ℕ → Pt := fun n => ((u, (Z n).1.2.2), (Z n).1.1)
  have hs1 : ∀ k, ∃ π, ∃ μ ∈ box 1, Q1 (k + 1) = par (Q1 k) π μ := by
    intro k
    obtain ⟨ht, ⟨π, π', hP, hQ⟩, _⟩ := hf (Z k)
    refine ⟨π, 0, by simp [box], ?_⟩
    simp only [Q1, hZ, par, add_zero]
    exact Prod.ext (Prod.ext rfl hP) ht
  have hs2 : ∀ k, ∃ π, ∃ μ ∈ box 1, Q2 (k + 1) = par (Q2 k) π μ := by
    intro k
    obtain ⟨ht, ⟨π, π', hP, hQ⟩, _⟩ := hf (Z k)
    refine ⟨π', 0, by simp [box], ?_⟩
    simp only [Q2, hZ, par, add_zero]
    exact Prod.ext (Prod.ext rfl hQ) ht
  obtain ⟨N1, hN1⟩ := hden ((u, P), t)
  obtain ⟨N2, hN2⟩ := hden ((u, Q), t)
  let N := max (max N1 N2) (2 * sep P Q + 1)
  have hN1' : N1 ≤ N := (le_max_left N1 N2).trans (le_max_left _ _)
  have hN2' : N2 ≤ N := (le_max_right N1 N2).trans (le_max_left _ _)
  have hd1 := hN1 N hN1' Q1 (by rfl) (fun k _ => hs1 k)
  have hd2 := hN2 N hN2' Q2 (by rfl) (fun k _ => hs2 k)
  let bad : ℕ → Prop := fun k => H E (Q1 k) ∨ H E (Q2 k)
  have hcard : ((Finset.range N).filter bad).card ≤
      ((Finset.range N).filter (fun k => H E (Q1 k))).card +
      ((Finset.range N).filter (fun k => H E (Q2 k))).card := by
    have heq : (Finset.range N).filter bad =
        ((Finset.range N).filter (fun k => H E (Q1 k))) ∪
        ((Finset.range N).filter (fun k => H E (Q2 k))) := by ext k; simp [bad, and_or_left]
    rw [heq]
    exact Finset.card_union_le _ _
  have hcardR : (((Finset.range N).filter bad).card : ℝ) ≤
      (((Finset.range N).filter (fun k => H E (Q1 k))).card : ℝ) +
      (((Finset.range N).filter (fun k => H E (Q2 k))).card : ℝ) := by exact_mod_cast hcard
  have hbad : (((Finset.range N).filter bad).card : ℝ) < 2 * delta * (N : ℝ) := by linarith
  have hdrift := distance_drift (fun n => sep (Z n).1.2.1 (Z n).1.2.2) bad
    (fun k => by
      have hh := (hf (Z k)).2.2
      simp only [hZ, bad, Q1, Q2]
      split_ifs with hb <;> simpa only [hb, ↓reduceIte] using hh) N
  have hfilter : @Finset.filter ℕ bad (fun i => Classical.propDecidable (bad i)) (Finset.range N) =
      (Finset.range N).filter bad := by ext i; simp only [Finset.mem_filter]
  rw [hfilter] at hdrift
  have hdriftR : (sep (Z N).1.2.1 (Z N).1.2.2 : ℝ) + (N : ℝ) ≤
      (sep P Q : ℝ) + ((D : ℝ) + 1) * (((Finset.range N).filter bad).card : ℝ) := by
    have hd : sep (Z N).1.2.1 (Z N).1.2.2 + N ≤ sep P Q +
        (D + 1) * ((Finset.range N).filter bad).card := by
      simpa only [Z, Function.iterate_zero_apply, z0] using hdrift
    exact_mod_cast hd
  have hN : 2 * (sep P Q : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast (le_max_right (max N1 N2) _)
  have hsep : 0 ≤ (sep (Z N).1.2.1 (Z N).1.2.2 : ℝ) := by positivity
  rw [Const.delta_eq] at hbad
  norm_num [D] at hdriftR
  linarith

/-- The actual noise law gives coherence for every complete history on one common event. -/
theorem same_site_ae (R : WangSet) {e : ℝ} (h0 : 0 ≤ e) (he : e ≤ eps0) :
    ∀ᵐ ω ∂((natCA R).noiseLaw₂ e), ∀ X : ℤ → (natCA R).Config,
      (natCA R).IsComplete ω X → ∀ (t : ℤ) (u : Plane) (P Q : Fin 2 → ℤ) (a b : R),
        UL (fun s => dec (X s)) (marked (flagsOf ω)) t (u, P) a →
        UL (fun s => dec (X s)) (marked (flagsOf ω)) t (u, Q) b → a = b := by
  filter_upwards [Density.all_path_density (natCA R) h0 he] with ω hω
  intro X hX t u P Q a b h h'
  exact same_site (isHistory_of_complete hX) hω h h'

end FLD.Coh
