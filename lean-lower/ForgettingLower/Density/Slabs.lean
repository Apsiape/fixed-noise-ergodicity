/-
# Density lemma: greedy full-slab selection and accounting (D0/D1 leaves)

Positions increase into the past. An H occurrence at k has a marked parent
at depth k+1. A FULL contour at that parent has terminal depths in
[k+1, right k+1]. Thus it covers occurrence positions [k, right k].
`right` is not truncated at the end N of the original path.

These are finite combinatorial lemmas. They assume numerical interval data,
not the density or contour theorem. Instantiating them with actual contours
and counting the connected union remain separate proof obligations.
-/
import ForgettingLower.Statements
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace FLD.Density

open scoped BigOperators

/-- Selected full slabs cover every occurrence, and successive selected slabs
are strictly separated at their closed endpoints. -/
def IsSlabSelection (A S : Finset ℕ) (right : ℕ → ℕ) : Prop :=
  S ⊆ A ∧
  (∀ k ∈ A, ∃ i ∈ S, i ≤ k ∧ k ≤ right i) ∧
  (∀ i ∈ S, ∀ j ∈ S, i < j → right i < j)

/-- Greedily choose the least remaining occurrence and discard everything
through its full right endpoint. No endpoint is clipped to the path length. -/
theorem exists_slab_selection (A : Finset ℕ) (right : ℕ → ℕ)
    (hright : ∀ i, i ≤ right i) : ∃ S, IsSlabSelection A S right := by
  classical
  refine Finset.strongInductionOn A ?_
  intro A ih
  by_cases hA : A.Nonempty
  · let i := A.min' hA
    have hi : i ∈ A := Finset.min'_mem A hA
    have hmin : ∀ j ∈ A, i ≤ j := fun j hj => Finset.min'_le A j hj
    let T := A.filter (fun j => right i < j)
    have hTA : T ⊆ A := Finset.filter_subset _ _
    have hiT : i ∉ T := by simp [T, not_lt.mpr (hright i)]
    have hss : T ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨hTA, fun h => hiT (h.symm ▸ hi)⟩
    obtain ⟨S, hSsub, hScov, hSsep⟩ := ih T hss
    refine ⟨insert i S, ?_, ?_, ?_⟩
    · exact Finset.insert_subset_iff.mpr ⟨hi, hSsub.trans hTA⟩
    · intro k hk
      by_cases hkR : k ≤ right i
      · exact ⟨i, Finset.mem_insert_self _ _, hmin k hk, hkR⟩
      · have hkT : k ∈ T := Finset.mem_filter.mpr ⟨hk, by omega⟩
        obtain ⟨j, hj, hjk, hkRj⟩ := hScov k hkT
        exact ⟨j, Finset.mem_insert_of_mem hj, hjk, hkRj⟩
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · omega
        · exact (Finset.mem_filter.mp (hSsub hb)).2
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · have := (Finset.mem_filter.mp (hSsub ha)).2
          have := hright i
          omega
        · exact hSsep a ha b hb hab
  · refine ⟨∅, by simp [IsSlabSelection, Finset.not_nonempty_iff_eq_empty.mp hA]⟩

/-- Every occurrence is paid for by a selected closed interval. -/
theorem occurrence_card_le (A S : Finset ℕ) (right : ℕ → ℕ)
    (h : IsSlabSelection A S right) :
    A.card ≤ ∑ i ∈ S, (right i + 1 - i) := by
  classical
  have hsub : A ⊆ S.biUnion (fun i => Finset.Icc i (right i)) := by
    intro k hk
    obtain ⟨i, hi, hik, hki⟩ := h.2.1 k hk
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_Icc.mpr ⟨hik, hki⟩⟩
  calc
    A.card ≤ (S.biUnion (fun i => Finset.Icc i (right i))).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ S, (Finset.Icc i (right i)).card := Finset.card_biUnion_le
    _ = ∑ i ∈ S, (right i + 1 - i) := by simp

/-- A contour with f>=1 terminals pays for at most 12(f-1)+1 <=12f
occurrence positions. The full final interval may extend beyond N. -/
theorem occurrence_mass_le (A S : Finset ℕ) (right flags : ℕ → ℕ)
    (h : IsSlabSelection A S right)
    (hspan : ∀ i ∈ S, right i + 1 - i ≤ 12 * flags i) :
    A.card ≤ 12 * ∑ i ∈ S, flags i := by
  calc
    A.card ≤ ∑ i ∈ S, (right i + 1 - i) := occurrence_card_le A S right h
    _ ≤ ∑ i ∈ S, 12 * flags i := Finset.sum_le_sum hspan
    _ = 12 * ∑ i ∈ S, flags i := by rw [Finset.mul_sum]

/-- The strict skip rule makes the FULL terminal sets disjoint physical sets.
The time/depth coordinate need not be injective. -/
theorem terminal_sets_pairwise_disjoint {V : Type*} [DecidableEq V]
    (A S : Finset ℕ) (right : ℕ → ℕ) (F : ℕ → Finset V) (depth : V → ℕ)
    (h : IsSlabSelection A S right)
    (hbracket : ∀ i ∈ S, ∀ v ∈ F i, i + 1 ≤ depth v ∧ depth v ≤ right i + 1) :
    (S : Set ℕ).PairwiseDisjoint F := by
  intro i hi j hj hne
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  have hiB := hbracket i hi v hvi
  have hjB := hbracket j hj v hvj
  rcases lt_or_gt_of_ne hne with hij | hji
  · have := h.2.2 i hi j hj hij
    omega
  · have := h.2.2 j hj i hi hji
    omega

/-- Count DISTINCT physical flags, including every flag of the uncut last contour. -/
theorem terminal_union_card {V : Type*} [DecidableEq V]
    (A S : Finset ℕ) (right : ℕ → ℕ) (F : ℕ → Finset V) (depth : V → ℕ)
    (h : IsSlabSelection A S right)
    (hbracket : ∀ i ∈ S, ∀ v ∈ F i, i + 1 ≤ depth v ∧ depth v ≤ right i + 1) :
    (S.biUnion F).card = ∑ i ∈ S, (F i).card :=
  Finset.card_biUnion (terminal_sets_pairwise_disjoint A S right F depth h hbracket)

/-- The contour span plus its one parent spur costs at most 12f. -/
theorem spur_contour_cost (f : ℕ) (hf : 1 ≤ f) : 1 + 12 * (f - 1) ≤ 12 * f := by
  omega

/-- Density pays for the entropy of the WHOLE length-N path: N<=16848f. -/
theorem whole_path_paid (N h f : ℕ) (hdense : (N : ℝ) / 1404 ≤ h)
    (hcover : h ≤ 12 * f) : N ≤ 16848 * f := by
  have hc : (h : ℝ) ≤ 12 * (f : ℝ) := by exact_mod_cast hcover
  have hn : (N : ℝ) ≤ 16848 * (f : ℝ) := by linarith
  exact_mod_cast hn

/-- The whole path, every spur, and every full contour fit in 16860f edges. -/
theorem whole_union_paid (N h f n : ℕ) (hdense : (N : ℝ) / 1404 ≤ h)
    (hcover : h ≤ 12 * f) (hedges : n ≤ N + 12 * f) : n ≤ densityCost * f := by
  have := whole_path_paid N h f hdense hcover
  dsimp [densityCost]
  omega

/-- The span bound at a selected contour implies its closed-interval charge. -/
theorem interval_cost (i r f : ℕ) (hir : i ≤ r) (hf : 1 ≤ f)
    (hspan : r - i ≤ 12 * (f - 1)) : r + 1 - i ≤ 12 * f := by
  omega

/-- Full skip/slab accounting, assembled without any truncation or assumptions
about independence. The data give a full contour flag set F i for every H
occurrence i; its closed terminal bracket and 12(f-1) span are explicit.
The result chooses disjoint full slabs, counts distinct flags, covers every
occurrence, and pays for the ENTIRE N-edge path plus all spurs and contours.
Constructing connected physical edge sets and proving contour existence are
not premises disguised as density; they remain separate nodes in BLUEPRINT. -/
theorem exists_density_accounting {V : Type*} [DecidableEq V]
    (A : Finset ℕ) (right : ℕ → ℕ) (F : ℕ → Finset V) (depth : V → ℕ) (N : ℕ)
    (hright : ∀ i, i ≤ right i)
    (hpos : ∀ i ∈ A, 1 ≤ (F i).card)
    (hspan : ∀ i ∈ A, right i - i ≤ 12 * ((F i).card - 1))
    (hbracket : ∀ i ∈ A, ∀ v ∈ F i, i + 1 ≤ depth v ∧ depth v ≤ right i + 1)
    (hdense : (N : ℝ) / 1404 ≤ A.card) :
    ∃ S : Finset ℕ, IsSlabSelection A S right ∧
      (S.biUnion F).card = ∑ i ∈ S, (F i).card ∧
      A.card ≤ 12 * (S.biUnion F).card ∧
      N + (∑ i ∈ S, (1 + 12 * ((F i).card - 1))) ≤
        densityCost * (S.biUnion F).card := by
  obtain ⟨S, hS⟩ := exists_slab_selection A right hright
  have hcard := terminal_union_card A S right F depth hS
    (fun i hi => hbracket i (hS.1 hi))
  have hmass := occurrence_mass_le A S right (fun i => (F i).card) hS
    (fun i hi => interval_cost i (right i) (F i).card (hright i)
      (hpos i (hS.1 hi)) (hspan i (hS.1 hi)))
  refine ⟨S, hS, hcard, ?_, ?_⟩
  · rwa [hcard]
  · rw [hcard]
    apply whole_union_paid N A.card (∑ i ∈ S, (F i).card) _ hdense hmass
    apply Nat.add_le_add_left
    calc
      (∑ i ∈ S, (1 + 12 * ((F i).card - 1))) ≤ ∑ i ∈ S, 12 * (F i).card :=
        Finset.sum_le_sum (fun i hi => spur_contour_cost (F i).card (hpos i (hS.1 hi)))
      _ = 12 * ∑ i ∈ S, (F i).card := by rw [Finset.mul_sum]

end FLD.Density
