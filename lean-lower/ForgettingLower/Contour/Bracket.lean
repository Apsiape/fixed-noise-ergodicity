/-
A sharpening of UND's copied-arm span lemma. Every witness vertex reaches an
actual arm terminal, so its time is bounded below by an actual selected flag.
This is the extra bracket needed by the density lemma's strict skip rule.
-/
import UncomputableNoiseDiagram.Contour.Grouped

set_option autoImplicit false

namespace FLD.Contour

open Relation UND.Contour

variable {V C Γ : Type*} (S : GroupedSystem V C Γ) [DecidableEq V]

/-- A vertex on a greedy arm reaches that arm's actual end. -/
theorem gEdges_reach_end (c : C) (θ : V) :
    ∀ e ∈ S.gEdges c θ, ∀ v ∈ e, S.Reach v (S.gEnd c θ) := by
  classical
  refine S.g_induction c (P := fun θ =>
    ∀ e ∈ S.gEdges c θ, ∀ v ∈ e, S.Reach v (S.gEnd c θ))
    (fun θ h ih => ?_) (fun θ h => ?_) θ
  · intro e he v hv
    rw [S.gEdges_of_step c h, Finset.mem_insert] at he
    rw [S.gEnd_of_step c h]
    rcases he with rfl | he
    · rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact (S.reach_g h).trans (S.reach_gEnd c _)
      · exact S.reach_gEnd c _
    · exact ih e he v hv
  · intro e he
    rw [S.gEdges_of_isTerm c h] at he
    simp at he

/-- The initial copied edge has the same terminal as the rest of its arm. -/
theorem pEdges_reach_end (σ : GroupedSystem.Pole V C) (c : C) (hσ : S.NF σ.loc) :
    ∀ e ∈ S.pEdges σ c, ∀ v ∈ e, S.Reach v (S.pEnd σ c) := by
  intro e he v hv
  rcases Finset.mem_insert.mp he with rfl | he
  · rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact (S.reach_sup hσ _).trans (S.reach_gEnd c _)
    · exact S.reach_gEnd c _
  · exact gEdges_reach_end S c (S.pFirst σ c) e he v hv

/-- Every vertex of the full witness reaches some actual arm terminal. -/
theorem witness_reach_end [Fintype C] {ρ : V} {P : Finset (GroupedSystem.Pole V C)}
    (hvalid : ∀ σ ∈ P, S.Valid ρ σ) :
    ∀ e ∈ S.witness P, ∀ v ∈ e,
      ∃ σ ∈ P, ∃ c, S.Reach v (S.pEnd σ c) := by
  classical
  intro e he v hv
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨σ, hσ, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨c, -, he⟩ := Finset.mem_biUnion.mp he
    exact ⟨σ, hσ, c, pEdges_reach_end S σ c (hvalid σ hσ).2 e he v hv⟩
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    have hp' := (Finset.mem_filter.mp hp).1
    simp only [Finset.mem_product, Finset.mem_univ, and_true] at hp'
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ⟨_, hp'.1, _, ReflTransGen.refl⟩
    · exact ⟨_, hp'.2, _, ReflTransGen.refl⟩

/-- Lower bound by one of the actual fixed-charge terminals, upper bound by root.
No replacement of the earliest terminal by root minus edge count is made. -/
theorem witness_terminal_bracket [Fintype C] (time : V → ℤ)
    (hsup : ∀ θ b, S.NF θ → time (S.sup θ b) + 1 = time θ)
    (hun : ∀ θ, S.UN θ → time (S.un θ) = time θ)
    (hgrp : ∀ φ φ', S.IsTerm φ → S.IsTerm φ' → S.grp φ = S.grp φ' → time φ = time φ')
    {ρ : V} {P : Finset (GroupedSystem.Pole V C)} (c0 : C)
    (hvalid : ∀ σ ∈ P, S.Valid ρ σ)
    (hsurj : ∀ σ ∈ P, ∀ c c', ∃ σ' ∈ P, S.pGrp σ' c' = S.pGrp σ c) :
    ∀ e ∈ S.witness P, ∀ v ∈ e,
      ∃ σ ∈ P, time (S.pEnd σ c0) ≤ time v ∧ time v ≤ time ρ := by
  intro e he v hv
  obtain ⟨σ, hσ, c, hr⟩ := witness_reach_end S hvalid e he v hv
  obtain ⟨σ', hσ', hg⟩ := hsurj σ hσ c c0
  have ht := hgrp _ _ (S.pEnd_isTerm σ' c0) (S.pEnd_isTerm σ c) hg
  refine ⟨σ', hσ', ?_, S.time_le_of_reach time hsup hun (S.witness_reach hvalid e he v hv)⟩
  rw [ht]
  exact S.time_le_of_reach time hsup hun hr

end FLD.Contour