/- The 720 injective shifted pairs and the transverse l1 distance. -/
import ForgettingLower.Geometry.Marked

set_option autoImplicit false

noncomputable section
namespace FLD.Coh
open FLD.Geometry

abbrev PSrc := Option (Fin 2) × Fin 15 × (Fin 1 → Fin 16)

theorem card_PSrc : Fintype.card PSrc = 3 * 15 * 16 := by
  simp [Fintype.card_prod, Fintype.card_option]

/-- The upper provider of a pair: block coordinate `x + 1` at `j`. -/
def pHi (j : Fin 2) (s : PSrc) : Provider := (s.1, Fin.insertNth j s.2.1.succ s.2.2)

/-- The lower provider of a pair: block coordinate `x` at `j`. -/
def pLo (j : Fin 2) (s : PSrc) : Provider := (s.1, Fin.insertNth j s.2.1.castSucc s.2.2)

theorem insertNth_inj {j : Fin 2} {x x' : Fin 16} {r r' : Fin 1 → Fin 16}
    (h : (Fin.insertNth j x r : Fin 2 → Fin 16) = Fin.insertNth j x' r') : x = x' ∧ r = r' := by
  refine ⟨?_, funext fun i => ?_⟩
  · have := congrFun h j
    rwa [Fin.insertNth_apply_same, Fin.insertNth_apply_same] at this
  · have := congrFun h (j.succAbove i)
    rwa [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove] at this

theorem pHi_injective (j : Fin 2) : Function.Injective (pHi j) := by
  rintro ⟨c, x, r⟩ ⟨c', x', r'⟩ h
  simp only [pHi, Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  obtain ⟨hx, rfl⟩ := insertNth_inj h2
  rw [Fin.succ_inj.1 hx]

theorem pLo_injective (j : Fin 2) : Function.Injective (pLo j) := by
  rintro ⟨c, x, r⟩ ⟨c', x', r'⟩ h
  simp only [pLo, Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  obtain ⟨hx, rfl⟩ := insertNth_inj h2
  rw [Fin.castSucc_inj.1 hx]

/-- The two providers of a pair differ by the unit vector `e_j`. -/
theorem offset_pair (j : Fin 2) (s : PSrc) (i : Fin 2) :
    offset (pHi j s) i = offset (pLo j s) i + if i = j then 1 else 0 := by
  simp only [offset, pHi, pLo, Pi.add_apply]
  by_cases hi : i = j
  · subst hi
    rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same, ite_eq_left rfl, Fin.val_succ,
      Fin.val_castSucc]
    push_cast; ring
  · obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hi
    rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove, ite_eq_right hi, add_zero]

/-- **The three-box pairing count**: if at most `|Bad₁| + |Bad₂| < 3·15·16 = 720` providers are discarded on
the two sides, some pair survives. -/
theorem exists_pair (f1 f2 : PSrc → Provider) (h1 : Function.Injective f1)
    (h2 : Function.Injective f2) (Bad1 Bad2 : Finset Provider)
    (h : Bad1.card + Bad2.card < 3 * 15 * 16) : ∃ s, f1 s ∉ Bad1 ∧ f2 s ∉ Bad2 := by
  classical
  by_contra hc
  push Not at hc
  have hA : (Finset.univ.filter fun s => f1 s ∈ Bad1).card ≤ Bad1.card :=
    Finset.card_le_card_of_injOn f1 (fun s hs => (Finset.mem_filter.1 hs).2)
      (fun a _ b _ e => h1 e)
  have hB : (Finset.univ.filter fun s => f2 s ∈ Bad2).card ≤ Bad2.card :=
    Finset.card_le_card_of_injOn f2 (fun s hs => (Finset.mem_filter.1 hs).2)
      (fun a _ b _ e => h2 e)
  have hU : (Finset.univ : Finset PSrc) ⊆ (Finset.univ.filter fun s => f1 s ∈ Bad1) ∪
      (Finset.univ.filter fun s => f2 s ∈ Bad2) := by
    intro s _
    by_cases hs : f1 s ∈ Bad1
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc s hs⟩)
  have := (Finset.card_le_card hU).trans (Finset.card_union_le _ _)
  rw [Finset.card_univ, card_PSrc] at this
  omega

/-! ## Providerider separation -/

/-- The provider separation `‖P' - P‖₁`. -/
def sep (P P' : Fin 2 → ℤ) : ℕ := ∑ i, (P' i - P i).natAbs

theorem sep_zero {P P' : Fin 2 → ℤ} (h : sep P P' = 0) : P = P' := by
  funext i
  have := (Finset.sum_eq_zero_iff.1 h) i (Finset.mem_univ _)
  omega

theorem sep_step {P P' : Fin 2 → ℤ} {j : Fin 2} (o o' : Fin 2 → ℤ)
    (ho : ∀ i, o' i = o i - if i = j then Int.sign (P' j - P j) else 0) (hj : P j ≠ P' j) :
    sep (P + o) (P' + o') + 1 = sep P P' := by
  have key : ∀ i, ((P' + o') i - (P + o) i).natAbs + (if i = j then 1 else 0) =
      (P' i - P i).natAbs := by
    intro i
    simp only [Pi.add_apply, ho]
    by_cases hi : i = j
    · subst hi
      simp only [↓reduceIte]
      rcases lt_or_gt_of_ne hj with h | h
      · rw [Int.sign_eq_one_of_pos (by omega)]; omega
      · rw [Int.sign_eq_neg_one_of_neg (by omega)]; omega
    · simp only [hi, ↓reduceIte]; omega
  simp only [sep]
  rw [← Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp



/-- Every provider coordinate lies between 0 and 175. -/
theorem offset_bounds (π : Provider) (i : Fin 2) : 0 ≤ offset π i ∧ offset π i ≤ 175 := by
  obtain ⟨c, o⟩ := π
  have := (o i).isLt
  cases c with
  | none => simp [offset, corner]; omega
  | some j => simp only [offset, corner, Pi.add_apply]; split_ifs <;> omega

/-- The printed diameter 350 bounds the l1 separation of any two offsets. -/
theorem sep_offset_le (π π' : Provider) : sep (offset π) (offset π') ≤ D := by
  have h0 := offset_bounds π 0
  have h1 := offset_bounds π 1
  have h0' := offset_bounds π' 0
  have h1' := offset_bounds π' 1
  simp only [sep, Fin.sum_univ_two, D]
  omega

/-- Arbitrary provider choices grow the distance by at most the printed D. -/
theorem sep_add_le (P Q : Fin 2 → ℤ) (π π' : Provider) :
    sep (P + offset π) (Q + offset π') ≤ sep P Q + D := by
  have h : sep (P + offset π) (Q + offset π') ≤ sep P Q + sep (offset π) (offset π') := by
    unfold sep
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have he : (Q + offset π') i - (P + offset π) i =
        (Q i - P i) + (offset π' i - offset π i) := by simp only [Pi.add_apply]; ring
    rw [he]
    exact Int.natAbs_add_le _ _
  exact h.trans (Nat.add_le_add_left (sep_offset_le π π') _)

end FLD.Coh
