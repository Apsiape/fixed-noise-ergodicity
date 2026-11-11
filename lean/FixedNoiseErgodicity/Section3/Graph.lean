/-
# The space-time graph `𝒢` (Section 3.4) and `fgt:count` for it

`𝒢` has vertex set `ℤ² × ℤᵏ × {0, 1, 2, …}`; each `(u, P, t)` with `t ≥ 1` is joined to its
*lower neighbours* `(u + d, P + c_i, t - 1)`, `d ∈ {-1,0,1}²`, `0 ≤ i ≤ k`. Every vertex has at
most `9q` lower and `9q` upper neighbours, so every degree is at most `18q ≤ D₀ = 50q`.
Here we define `𝒢`, its neighbour finsets, and instantiate the abstract count
`EdgeCount.card_le_pow` (`fgt:count` = `mem:count`). The memory graph `H_k` of Section 4 has the
same edges on `ℤ` times; every set of edges used there lies at positive times, so `𝒢` serves
both sections.
-/
import FixedNoiseErgodicity.Section3.Transport
import FixedNoiseErgodicity.Combinatorics.EdgeCount

set_option autoImplicit false

noncomputable section

namespace FNE

variable {k : ℕ}

/-- Space-time points `(v, t)`, the vertices of `𝒢`. -/
abbrev STPoint (k : ℕ) := Site k × ℕ

/-- `fgt:sec-contour`. `θ'` is a *lower neighbour of `θ` through provider `i`*:
`θ = (u, P, t)` with `t ≥ 1` and `θ' = (u + d, P + c_i, t - 1)` for some `d ∈ {-1,0,1}²`. -/
def IsLowerNbr (θ θ' : STPoint k) (i : Option (Fin k)) : Prop :=
  θ'.2 + 1 = θ.2 ∧ ∃ d ∈ box 1, θ'.1 = (θ.1.1 + d, θ.1.2 + provider k i)

/-- `fgt:sec-contour`. The edges of `𝒢`: `{θ, θ'}` with `θ'` a lower neighbour of `θ`. -/
def IsGEdge (e : Sym2 (STPoint k)) : Prop :=
  ∃ θ θ' : STPoint k, ∃ i : Option (Fin k), IsLowerNbr θ θ' i ∧ e = s(θ, θ')

/-- The lower neighbours of `θ`, as a finset. -/
def lowerNbrs (θ : STPoint k) : Finset (STPoint k) :=
  if θ.2 = 0 then ∅ else
    (box 1 ×ˢ (Finset.univ : Finset (Option (Fin k)))).image
      (fun p => ((θ.1.1 + p.1, θ.1.2 + provider k p.2), θ.2 - 1))

/-- The upper neighbours of `θ`, as a finset. -/
def upperNbrs (θ : STPoint k) : Finset (STPoint k) :=
  (box 1 ×ˢ (Finset.univ : Finset (Option (Fin k)))).image
    (fun p => ((θ.1.1 - p.1, θ.1.2 - provider k p.2), θ.2 + 1))

/-- All neighbours of `θ` in `𝒢`. -/
def gNbrs (θ : STPoint k) : Finset (STPoint k) := lowerNbrs θ ∪ upperNbrs θ

theorem card_box_one : (box 1).card = 9 := by
  simp [box]

theorem card_upperNbrs_le (θ : STPoint k) : (upperNbrs θ).card ≤ 9 * (k + 1) := by
  unfold upperNbrs
  refine Finset.card_image_le.trans ?_
  simp [Finset.card_product, card_box_one]

theorem card_lowerNbrs_le (θ : STPoint k) : (lowerNbrs θ).card ≤ 9 * (k + 1) := by
  unfold lowerNbrs
  split_ifs
  · simp
  · refine Finset.card_image_le.trans ?_
    simp [Finset.card_product, card_box_one]

/-- Every vertex of `𝒢` has at most `18q` neighbours. -/
theorem card_gNbrs_le (θ : STPoint k) : (gNbrs θ).card ≤ 18 * (k + 1) := by
  unfold gNbrs
  refine (Finset.card_union_le _ _).trans ?_
  have := card_lowerNbrs_le θ
  have := card_upperNbrs_le θ
  omega

/-- `18q ≤ D₀ = 50q`. -/
theorem card_gNbrs_le_D0 (θ : STPoint k) : (gNbrs θ).card ≤ 50 * (k + 1) :=
  (card_gNbrs_le θ).trans (by omega)

/-- Both ends of a `𝒢`-edge are neighbours of each other. -/
theorem mem_gNbrs_of_lower {θ θ' : STPoint k} {i : Option (Fin k)} (h : IsLowerNbr θ θ' i) :
    θ' ∈ gNbrs θ ∧ θ ∈ gNbrs θ' := by
  obtain ⟨ht, d, hd, hv⟩ := h
  obtain ⟨⟨u, P⟩, t⟩ := θ
  obtain ⟨v', t'⟩ := θ'
  simp only at ht hv
  subst hv
  constructor
  · refine Finset.mem_union_left _ ?_
    unfold lowerNbrs
    rw [if_neg (by simp only; omega)]
    refine Finset.mem_image.mpr ⟨(d, i), by simp [hd], ?_⟩
    simp only [Prod.mk.injEq, true_and]
    omega
  · refine Finset.mem_union_right _ ?_
    unfold upperNbrs
    refine Finset.mem_image.mpr ⟨(d, i), by simp [hd], ?_⟩
    simp only [Prod.mk.injEq, add_sub_cancel_right, true_and]
    exact ht

/-- If every edge of `K` is an edge of `𝒢`, then `s(a, b) ∈ K` implies that `b` is a neighbour of
`a`. -/
theorem nbr_of_gEdges {K : Finset (Sym2 (STPoint k))} (hK : ∀ e ∈ K, IsGEdge e) :
    ∀ a b, s(a, b) ∈ K → b ∈ gNbrs a := by
  intro a b hab
  obtain ⟨θ, θ', i, hl, he⟩ := hK _ hab
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (mem_gNbrs_of_lower hl).1
  · exact (mem_gNbrs_of_lower hl).2

/-- **`fgt:count` for `𝒢`** (= `mem:count` for `H_k`). For every vertex `θ₀` and `n`, every finite
family of `n`-edge sets of `𝒢` that are connected at `θ₀` has at most `(18q)^{2n}` members. -/
theorem gCount (θ₀ : STPoint k) (n : ℕ) (S : Finset (Finset (Sym2 (STPoint k))))
    (hS : ∀ K ∈ S, K.card = n ∧ (∀ e ∈ K, IsGEdge e) ∧ EdgeCount.ConnectedAt K θ₀) :
    S.card ≤ (18 * (k + 1)) ^ (2 * n) :=
  EdgeCount.card_le_pow gNbrs _ card_gNbrs_le θ₀ n S
    fun K hK => ⟨(hS K hK).1, nbr_of_gEdges (hS K hK).2.1, (hS K hK).2.2⟩

/-- **`fgt:count`** as printed: at most `D₀^{2n}` such sets, `D₀ = 50q`. -/
theorem gCount_D0 (θ₀ : STPoint k) (n : ℕ) (S : Finset (Finset (Sym2 (STPoint k))))
    (hS : ∀ K ∈ S, K.card = n ∧ (∀ e ∈ K, IsGEdge e) ∧ EdgeCount.ConnectedAt K θ₀) :
    S.card ≤ (50 * (k + 1)) ^ (2 * n) :=
  (gCount θ₀ n S hS).trans (Nat.pow_le_pow_left (by omega) _)

/-- The set of connected `n`-edge sets of `𝒢` at `θ₀` is finite, with at most `D₀^{2n}`
elements (the form used in the Peierls sums). -/
theorem finite_connected (θ₀ : STPoint k) (n : ℕ) :
    {K : Finset (Sym2 (STPoint k)) |
      K.card = n ∧ (∀ e ∈ K, IsGEdge e) ∧ EdgeCount.ConnectedAt K θ₀}.Finite ∧
    {K : Finset (Sym2 (STPoint k)) |
      K.card = n ∧ (∀ e ∈ K, IsGEdge e) ∧ EdgeCount.ConnectedAt K θ₀}.ncard ≤
        (50 * (k + 1)) ^ (2 * n) := by
  set A := {K : Finset (Sym2 (STPoint k)) |
      K.card = n ∧ (∀ e ∈ K, IsGEdge e) ∧ EdgeCount.ConnectedAt K θ₀}
  have hfin : A.Finite := by
    by_contra hinf
    obtain ⟨S, hSA, hScard⟩ :=
      Set.Infinite.exists_subset_card_eq hinf ((50 * (k + 1)) ^ (2 * n) + 1)
    have := gCount_D0 θ₀ n S (fun K hK => hSA hK)
    omega
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card A hfin]
  exact gCount_D0 θ₀ n _ (fun K hK => (Set.Finite.mem_toFinset hfin).mp hK)

end FNE

end
