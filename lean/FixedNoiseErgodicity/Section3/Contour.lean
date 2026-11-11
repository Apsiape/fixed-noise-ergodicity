/-
# `lem:contour` on the graph `𝒢` (Section 3.4)

The abstract contour lemma (`Combinatorics/Contour.lean`) is instantiated with
* vertices `(v, t)` of `𝒢`, time `t`;
* non-terminal vertices: `𝒰 \ 𝒰_f`; supports: two lower neighbours in `𝒰` through different
  providers, chosen once and for all (Step 1);
* charges: the providers `Option (Fin k)` (`none` is `c_0`), so `q = k + 1`;
* potentials `ψ_0(P, t) = q(P_1 + … + P_k) + k t` and `ψ_i(P, t) = -q P_i - t`.
-/
import FixedNoiseErgodicity.Section3.Graph
import FixedNoiseErgodicity.Combinatorics.Contour

set_option autoImplicit false

noncomputable section

namespace FNE

open Relation

variable {k : ℕ}

/-! ## The potentials (Step 2) -/

/-- Step 2: `ψ_0(P, t) = q(P_1 + ⋯ + P_k) + k t` and `ψ_i(P, t) = -q P_i - t`. -/
def psiG (k : ℕ) : Option (Fin k) → STPoint k → ℤ
  | none, θ => ((k : ℤ) + 1) * ∑ i, θ.1.2 i + (k : ℤ) * (θ.2 : ℤ)
  | some i, θ => -(((k : ℤ) + 1) * θ.1.2 i) - (θ.2 : ℤ)

/-- `fgt:eq-sum`. -/
theorem psiG_sum (θ : STPoint k) : ∑ c, psiG k c θ = 0 := by
  rw [Fintype.sum_option]
  simp only [psiG]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- `fgt:eq-incr`: along an edge to a lower neighbour through provider `p`, `ψ_c` rises by `1`
if `p ≠ c` and falls by `k` if `p = c`. -/
theorem psiG_step {θ θ' : STPoint k} {p : Option (Fin k)} (h : IsLowerNbr θ θ' p)
    (c : Option (Fin k)) :
    psiG k c θ' = psiG k c θ + 1 -
      (if p = c then (Fintype.card (Option (Fin k)) : ℤ) else 0) := by
  obtain ⟨ht, d, -, hv⟩ := h
  have hP : θ'.1.2 = θ.1.2 + provider k p := by rw [hv]
  have ht' : (θ'.2 : ℤ) = (θ.2 : ℤ) - 1 := by omega
  simp only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  cases c with
  | none =>
    simp only [psiG, hP, ht', Pi.add_apply, Finset.sum_add_distrib]
    cases p with
    | none => simp [provider]; ring
    | some j =>
      simp only [provider, reduceCtorEq, if_false]
      rw [Finset.sum_pi_single']
      simp only [Finset.mem_univ, if_true]
      ring
  | some i =>
    simp only [psiG, hP, ht', Pi.add_apply]
    cases p with
    | none => simp [provider]; ring
    | some j =>
      simp only [provider, Option.some.injEq]
      by_cases hij : j = i
      · subst hij
        simp only [Pi.single_eq_same, if_true]
        ring
      · rw [Pi.single_eq_of_ne (Ne.symm hij), if_neg hij]
        ring

/-! ## The support system of a set `𝒰` with faults `𝒰_f` (Step 1) -/

/-- The hypothesis of `lem:contour`: every vertex of `𝒰 \ 𝒰_f` has two lower neighbours in `𝒰`
through different providers. -/
def HasSupports (U Uf : Set (STPoint k)) : Prop :=
  ∀ θ ∈ U, θ ∉ Uf → ∃ θ₁ θ₂ : STPoint k, ∃ i₁ i₂ : Option (Fin k), i₁ ≠ i₂ ∧
    IsLowerNbr θ θ₁ i₁ ∧ IsLowerNbr θ θ₂ i₂ ∧ θ₁ ∈ U ∧ θ₂ ∈ U

/-- **`lem:contour`.** Let `𝒰` be a set of vertices of `𝒢` and `𝒰_f ⊆ 𝒰` the faults, and suppose
that every vertex of `𝒰 \ 𝒰_f` has two lower neighbours in `𝒰` through different providers. Let
`ρ ∈ 𝒰 \ 𝒰_f`. Then there are `m ≥ 2`, a set `Σ ⊆ 𝒰_f` of `m` faults and a finite set `K` of
edges of `𝒢` such that
(i) `K` is connected (at `ρ`); each edge joins a vertex of `𝒰 \ 𝒰_f` to one of its lower
neighbours in `𝒰`; `ρ` and every point of `Σ` are vertices of `K`;
(ii) `1 ≤ |K| ≤ q²(m - 1)`;
(iii) with `s` the least time of a point of `Σ`, every vertex of `K` has time in `[s, t_ρ]`, and
`t_ρ - s ≤ q²(m - 1)`.
(The paper also assumes that all vertices of `𝒰` have positive time; the proof does not use it.) -/
theorem contourG (U Uf : Set (STPoint k)) (hsupp : HasSupports U Uf) {ρ : STPoint k}
    (hρU : ρ ∈ U) (hρ : ρ ∉ Uf) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ (Sig : Finset (STPoint k)) (K : Finset (Sym2 (STPoint k))),
      (∀ φ ∈ Sig, φ ∈ Uf) ∧ Sig.card = m ∧
      EdgeCount.ConnectedAt K ρ ∧
      (∀ e ∈ K, ∃ θ θ' : STPoint k, ∃ i : Option (Fin k),
        θ ∈ U ∧ θ ∉ Uf ∧ IsLowerNbr θ θ' i ∧ θ' ∈ U ∧ e = s(θ, θ')) ∧
      (∃ e ∈ K, ρ ∈ e) ∧ (∀ φ ∈ Sig, ∃ e ∈ K, φ ∈ e) ∧
      1 ≤ K.card ∧ K.card ≤ (k + 1) ^ 2 * (m - 1) ∧
      ∃ s : ℕ, (∃ φ ∈ Sig, φ.2 = s) ∧ (∀ φ ∈ Sig, s ≤ φ.2) ∧
        (∀ e ∈ K, ∀ v ∈ e, s ≤ v.2 ∧ v.2 ≤ ρ.2) ∧ ρ.2 - s ≤ (k + 1) ^ 2 * (m - 1) := by
  classical
  choose! s₁ s₂ p₁ p₂ hne hl₁ hl₂ hU₁ hU₂ using hsupp
  let S : Contour.SupportSystem (STPoint k) (Option (Fin k)) :=
    { time := Prod.snd
      NF := fun θ => θ ∈ U ∧ θ ∉ Uf
      sup := fun θ b => if b then s₁ θ else s₂ θ
      prov := fun θ b => if b then p₁ θ else p₂ θ
      prov_ne := fun θ h => by simpa using hne θ h.1 h.2
      time_sup := fun θ b h => by
        cases b
        · exact (hl₂ θ h.1 h.2).1
        · exact (hl₁ θ h.1 h.2).1 }
  have hlow : ∀ θ b, S.NF θ → IsLowerNbr θ (S.sup θ b) (S.prov θ b) ∧ S.sup θ b ∈ U := by
    intro θ b h
    cases b
    · exact ⟨hl₂ θ h.1 h.2, hU₂ θ h.1 h.2⟩
    · exact ⟨hl₁ θ h.1 h.2, hU₁ θ h.1 h.2⟩
  have hψ : S.IsPotential (psiG k) :=
    ⟨psiG_sum, fun θ b c h => psiG_step (hlow θ b h).1 c⟩
  have hreachU : ∀ {θ}, S.Reach ρ θ → θ ∈ U := by
    intro θ h
    induction h with
    | refl => exact hρU
    | tail _ hst _ =>
      obtain ⟨hnf, b, rfl⟩ := hst
      exact (hlow _ b hnf).2
  obtain ⟨Sig, K, hterm, hedge, hconn, hρK, hSigK, hK1, hKb, htime, hcross⟩ :=
    S.contour hψ (ρ := ρ) ⟨hρU, hρ⟩
  have hq : Fintype.card (Option (Fin k)) = k + 1 := by simp
  rw [hq] at hKb
  have hm2 : 2 ≤ Sig.card := by
    by_contra hlt
    have : (k + 1) ^ 2 * Sig.card ≤ (k + 1) ^ 2 * 1 := Nat.mul_le_mul_left _ (by omega)
    omega
  have hKle : K.card ≤ (k + 1) ^ 2 * (Sig.card - 1) := by
    rw [Nat.mul_sub_one]
    omega
  obtain ⟨φm, hφm, hmin⟩ := Sig.exists_min_image Prod.snd (Finset.card_pos.mp (by omega))
  refine ⟨Sig.card, hm2, Sig, K, fun φ hφ => ?_, rfl, hconn, fun e he => ?_, hρK, hSigK, hK1,
    hKle, φm.2, ⟨φm, hφm, rfl⟩, hmin, fun e he v hv => ?_, ?_⟩
  · obtain ⟨hr, hn⟩ := hterm φ hφ
    by_contra hφU
    exact hn ⟨hreachU hr, hφU⟩
  · obtain ⟨a, b, ha, hna, rfl⟩ := hedge e he
    exact ⟨a, S.sup a b, S.prov a b, hna.1, hna.2, (hlow a b hna).1, (hlow a b hna).2, rfl⟩
  · obtain ⟨h1, φ, hφ, h2⟩ := htime e he v hv
    exact ⟨(hmin φ hφ).trans h2, h1⟩
  · have h1 : ρ.2 ≤ φm.2 + K.card := hcross φm hφm
    show ρ.2 - φm.2 ≤ _
    omega

/-! ## The marked vertices and the events -/

/-- Marked vertices: `E_t(v) = 1` (the time is positive since `E_0 ≡ 0`). -/
def markedSet (η : ℕ × Site k → Bool) : Set (STPoint k) := {θ | domField η θ.2 θ.1}

/-- Events: `(v, t)` with `t ≥ 1` and `η_t(v) = 1` (noise index `t - 1`). -/
def eventSet (η : ℕ × Site k → Bool) : Set (STPoint k) :=
  {θ | ∃ t, θ.2 = t + 1 ∧ η (t, θ.1) = true}

/-- Paragraph after `lem:contour`: events are marked. -/
theorem eventSet_subset (η : ℕ × Site k → Bool) : eventSet η ⊆ markedSet η := by
  rintro ⟨v, t⟩ ⟨t', ht, hη⟩
  simp only at ht
  subst ht
  exact (domField_succ η t' v).mpr (Or.inl hη)

/-- Paragraph after `lem:contour`: a marked vertex that is not an event has two marked lower
neighbours through different providers. -/
theorem marked_hasSupports (η : ℕ × Site k → Bool) : HasSupports (markedSet η) (eventSet η) := by
  rintro ⟨v, t⟩ hm hev
  cases t with
  | zero => exact absurd hm (domField_zero η v)
  | succ t =>
    have hm' : domField η (t + 1) v := hm
    rcases (domField_succ η t v).mp hm' with h | ⟨i, i', hii', d, hd, d', hd', h1, h2⟩
    · exact absurd ⟨t, rfl, h⟩ hev
    · exact ⟨((v.1 + d, v.2 + provider k i), t), ((v.1 + d', v.2 + provider k i'), t), i, i',
        hii', ⟨rfl, d, hd, rfl⟩, ⟨rfl, d', hd', rfl⟩, h1, h2⟩

/-- **`lem:contour`, last assertion.** Fix the indicators `η`. If `E_{t+1}(v) = 1` and `(v, t+1)`
is not an event, there is a set `K` of `n = |K| ≥ 1` edges of `𝒢`, each joining a vertex to one of
its lower neighbours, forming a connected graph containing `(v, t + 1)`, whose vertices include a
set `Σ` of `m` distinct events, with `n ≤ q²(m - 1)`. -/
theorem contour_marked (η : ℕ × Site k → Bool) {v : Site k} {t : ℕ}
    (hmark : domField η (t + 1) v) (hev : η (t, v) = false) :
    ∃ (K : Finset (Sym2 (STPoint k))) (Sig : Finset (STPoint k)),
      1 ≤ K.card ∧ (∀ e ∈ K, IsGEdge e) ∧ EdgeCount.ConnectedAt K (v, t + 1) ∧
      (∃ e ∈ K, (v, t + 1) ∈ e) ∧ (∀ φ ∈ Sig, ∃ e ∈ K, φ ∈ e) ∧
      (∀ φ ∈ Sig, φ ∈ eventSet η) ∧ K.card ≤ (k + 1) ^ 2 * (Sig.card - 1) := by
  have hnot : ((v, t + 1) : STPoint k) ∉ eventSet η := by
    rintro ⟨t', ht', hη⟩
    simp only [Nat.add_right_cancel_iff] at ht'
    subst ht'
    rw [hev] at hη
    exact Bool.false_ne_true hη
  obtain ⟨m, -, Sig, K, hSig, hcard, hconn, hedge, hρK, hSigK, hK1, hKle, -⟩ :=
    contourG (markedSet η) (eventSet η) (marked_hasSupports η) (ρ := (v, t + 1)) hmark hnot
  refine ⟨K, Sig, hK1, fun e he => ?_, hconn, hρK, hSigK, hSig, hcard ▸ hKle⟩
  obtain ⟨θ, θ', i, -, -, hl, -, rfl⟩ := hedge e he
  exact ⟨θ, θ', i, hl, rfl⟩

end FNE

end
