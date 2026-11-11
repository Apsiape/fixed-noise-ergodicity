/-
# Section 5: the substitutions `φ`, `φ'`, `σ` and their soundness

* `subst2`: blockwise `2 × 2` substitution of patterns, `φ(w)(2v + ς) = φ(w(v))(ς)`, and the
  generic criterion `legalOn_subst2_iff` (internal edges match, and the two fine edges across a
  seam match iff the coarse edge matches; then `φ(w)` is legal on `2U + [0,2)²` iff `w` is legal
  on `U`). This is the argument of `scf:base`(b) and `scf:ruler-forward`(b), stated once.
* `scf:def-phi` (`Formal.child`), `scf:base` (a), (b), (c).
* `scf:def-phiprime` (`Letter.child`, `sigma`, `sigmaPow`), `scf:ruler-forward` (a), (b), (c).
* `prop:scaffold` (i), (ii), (iv), (v) and the remark at 06:19 (`(φ')^{2n} = σ^n`).
**[choice]** A child `ς ∈ [0,2)²` is given by two Booleans `(ς₁ = 1, ς₂ = 1)`.
-/
import FixedNoiseErgodicity.Scaffold.Tables
import FixedNoiseErgodicity.Section2.Compact

set_option autoImplicit false

-- `child_inO_check` and `child_inA_check` walk the lists of 104 and 276 entries in the kernel.
-- Kernel checks are Boolean folds (`List.all … = true`): a `Decidable` instance for a bounded
-- quantifier over the same list builds proof terms at every step and needs more than 4 GB.
set_option maxRecDepth 20000

namespace FNE.Scaffold

/-! ## Blockwise `2 × 2` substitution of patterns -/

section Subst2

variable {α β : Type*}

/-- The bit `0` or `1` of a Boolean, as an integer. -/
def bitZ (s : Bool) : ℤ := if s then 1 else 0

/-- `scf:def-phi` (blockwise): `φ(w)(2v + ς) = φ(w(v))(ς)`. Children are indexed by two
Booleans, `ς = (bitZ s₁, bitZ s₂)`. -/
def subst2 (φ : α → Bool → Bool → β) (w : Plane → α) : Plane → β :=
  fun x => φ (w (x.1 / 2, x.2 / 2)) (decide (x.1 % 2 = 1)) (decide (x.2 % 2 = 1))

/-- The fine domain `2U + [0,2)²` of `φ(w)` for a pattern `w` on `U`. -/
def fine2 (U : Set Plane) : Set Plane := {x | (x.1 / 2, x.2 / 2) ∈ U}

/-- The fine site `2v + ς`. -/
def fineSite (v : Plane) (s1 s2 : Bool) : Plane := (2 * v.1 + bitZ s1, 2 * v.2 + bitZ s2)

theorem fineSite_div (v : Plane) (s1 s2 : Bool) :
    ((fineSite v s1 s2).1 / 2, (fineSite v s1 s2).2 / 2) = v := by
  obtain ⟨v1, v2⟩ := v
  cases s1 <;> cases s2 <;> simp only [fineSite, bitZ, Prod.mk.injEq] <;> omega

theorem subst2_fineSite (φ : α → Bool → Bool → β) (w : Plane → α) (v : Plane) (s1 s2 : Bool) :
    subst2 φ w (fineSite v s1 s2) = φ (w v) s1 s2 := by
  obtain ⟨v1, v2⟩ := v
  have hv := fineSite_div (v1, v2) s1 s2
  simp only [subst2]
  rw [hv]
  cases s1 <;> cases s2 <;> simp only [fineSite, bitZ] <;> congr <;> simp

theorem fineSite_mem {U : Set Plane} {v : Plane} {s1 s2 : Bool} :
    fineSite v s1 s2 ∈ fine2 U ↔ v ∈ U := by
  simp only [fine2, Set.mem_setOf_eq, fineSite_div]

theorem exists_fineSite (x : Plane) : ∃ v s1 s2, x = fineSite v s1 s2 := by
  refine ⟨(x.1 / 2, x.2 / 2), decide (x.1 % 2 = 1), decide (x.2 % 2 = 1), ?_⟩
  obtain ⟨x1, x2⟩ := x
  simp only [fineSite, bitZ, Prod.mk.injEq]
  constructor <;> split_ifs with h <;> simp_all <;> omega

theorem fineSite_false_add_e1 (v : Plane) (s2 : Bool) :
    fineSite v false s2 + (1, 0) = fineSite v true s2 := by
  simp only [fineSite, bitZ, Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> simp

theorem fineSite_true_add_e1 (v : Plane) (s2 : Bool) :
    fineSite v true s2 + (1, 0) = fineSite (v + (1, 0)) false s2 := by
  simp only [fineSite, bitZ, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.mk.injEq]
  exact ⟨by simp; ring, by simp⟩

theorem fineSite_false_add_e2 (v : Plane) (s1 : Bool) :
    fineSite v s1 false + (0, 1) = fineSite v s1 true := by
  simp only [fineSite, bitZ, Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> simp

theorem fineSite_true_add_e2 (v : Plane) (s1 : Bool) :
    fineSite v s1 true + (0, 1) = fineSite (v + (0, 1)) s1 false := by
  simp only [fineSite, bitZ, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.mk.injEq]
  exact ⟨by simp, by simp; ring⟩

/-- The argument of `scf:base`(b) and `scf:ruler-forward`(b), once for all `2 × 2`
substitutions. If the internal edges of every block `φ(a)` match, and the two fine edges across a
vertical (horizontal) seam between `φ(a)` and `φ(a')` both match exactly when `a, a'` match in
direction `e₁` (`e₂`), then `φ(w)` is legal on `2U + [0,2)²` if and only if `w` is legal on
`U`. -/
theorem legalOn_subst2_iff {Hα Vα : α → α → Prop} {Hβ Vβ : β → β → Prop}
    (φ : α → Bool → Bool → β)
    (inH : ∀ a s2, Hβ (φ a false s2) (φ a true s2))
    (inV : ∀ a s1, Vβ (φ a s1 false) (φ a s1 true))
    (seamH : ∀ a a', (Hβ (φ a true false) (φ a' false false) ∧
      Hβ (φ a true true) (φ a' false true)) ↔ Hα a a')
    (seamV : ∀ a a', (Vβ (φ a false true) (φ a' false false) ∧
      Vβ (φ a true true) (φ a' true false)) ↔ Vα a a')
    {U : Set Plane} {w : Plane → α} :
    LegalOn Hβ Vβ (fine2 U) (subst2 φ w) ↔ LegalOn Hα Vα U w := by
  constructor
  · rintro ⟨hH, hV⟩
    refine ⟨fun u hu hu' => (seamH _ _).1 ?_, fun u hu hu' => (seamV _ _).1 ?_⟩
    · have key : ∀ s2, Hβ (φ (w u) true s2) (φ (w (u + (1, 0))) false s2) := by
        intro s2
        have := hH (fineSite u true s2) (fineSite_mem.2 hu)
          (by rw [fineSite_true_add_e1]; exact fineSite_mem.2 hu')
        rwa [fineSite_true_add_e1, subst2_fineSite, subst2_fineSite] at this
      exact ⟨key false, key true⟩
    · have key : ∀ s1, Vβ (φ (w u) s1 true) (φ (w (u + (0, 1))) s1 false) := by
        intro s1
        have := hV (fineSite u s1 true) (fineSite_mem.2 hu)
          (by rw [fineSite_true_add_e2]; exact fineSite_mem.2 hu')
        rwa [fineSite_true_add_e2, subst2_fineSite, subst2_fineSite] at this
      exact ⟨key false, key true⟩
  · rintro ⟨hH, hV⟩
    refine ⟨fun x hx hx' => ?_, fun x hx hx' => ?_⟩
    · obtain ⟨v, s1, s2, rfl⟩ := exists_fineSite x
      cases s1
      · rw [fineSite_false_add_e1, subst2_fineSite, subst2_fineSite]; exact inH _ _
      · rw [fineSite_true_add_e1] at hx' ⊢
        rw [subst2_fineSite, subst2_fineSite]
        have h := (seamH _ _).2 (hH v (fineSite_mem.1 hx) (fineSite_mem.1 hx'))
        cases s2
        · exact h.1
        · exact h.2
    · obtain ⟨v, s1, s2, rfl⟩ := exists_fineSite x
      cases s2
      · rw [fineSite_false_add_e2, subst2_fineSite, subst2_fineSite]; exact inV _ _
      · rw [fineSite_true_add_e2] at hx' ⊢
        rw [subst2_fineSite, subst2_fineSite]
        have h := (seamV _ _).2 (hV v (fineSite_mem.1 hx) (fineSite_mem.1 hx'))
        cases s1
        · exact h.1
        · exact h.2

/-- Values of `φ(w)` on `2U + [0,2)²` are children of values of `w` on `U`. -/
theorem subst2_mem {P : α → Prop} {Q : β → Prop} (φ : α → Bool → Bool → β)
    (hφ : ∀ a, P a → ∀ s1 s2, Q (φ a s1 s2)) {U : Set Plane} {w : Plane → α}
    (hw : ∀ u ∈ U, P (w u)) : ∀ x ∈ fine2 U, Q (subst2 φ w x) := by
  intro x hx
  obtain ⟨v, s1, s2, rfl⟩ := exists_fineSite x
  rw [subst2_fineSite]
  exact hφ _ (hw v (fineSite_mem.1 hx)) s1 s2

end Subst2

/-! ## `φ` on formal triples (`scf:def-phi`, `scf:base`) -/

namespace Formal

/-- `scf:def-phi`, `scf:tab-subst` (left): the child `ς = (s₁, s₂)` of `φ(θ, κ, ω)`:
`(0,0) ↦ (a, κ, ω)`, `(1,0) ↦ (c, ⟨∂_S θ, ∂_E κ⟩, se ω)`, `(0,1) ↦ (d, ⟨∂_N κ, ∂_W θ⟩, nw ω)`,
`(1,1) ↦ (b, F(θ), A)`. Defined for every formal triple. -/
def child (t : Formal) : Bool → Bool → Formal
  | false, false => ⟨.a, t.thick, t.black⟩
  | true, false => ⟨.c, .line t.thin.epS t.thick.epE, se t.black⟩
  | false, true => ⟨.d, .line t.thick.epN t.thin.epW, nw t.black⟩
  | true, true => ⟨.b, .corner (F t.thin), .A⟩

/-- `scf:base`(a), first half: the four children of a tile of `𝕆` lie in `𝕆`
(a check over the 104 tiles). -/
theorem child_inO_check : (baseList.all fun t => [false, true].all fun s1 =>
    [false, true].all fun s2 => (t.child s1 s2).inO) = true := by
  decide +kernel

theorem InO.child {t : Formal} (h : t.InO) (s1 s2 : Bool) : (t.child s1 s2).InO := by
  have h1 := List.all_eq_true.1 child_inO_check t (mem_baseList.2 h)
  have h2 := List.all_eq_true.1 h1 s1 (by cases s1 <;> simp)
  exact List.all_eq_true.1 h2 s2 (by cases s2 <;> simp)

/-- `scf:base`(a), second half: the four internal edges of `φ(t)` match, for every formal
triple. -/
theorem child_matchE (t : Formal) (s2 : Bool) : MatchE (t.child false s2) (t.child true s2) := by
  rw [matchE_iff]
  cases s2
  · exact ⟨rfl, rfl, (se_spec t.black).2.symm⟩
  · exact ⟨rfl, (F_epW t.thin).symm, nw_bitE t.black⟩

theorem child_matchN (t : Formal) (s1 : Bool) : MatchN (t.child s1 false) (t.child s1 true) := by
  rw [matchN_iff]
  cases s1
  · exact ⟨rfl, rfl, (nw_spec t.black).2.symm⟩
  · exact ⟨rfl, (F_epS t.thin).symm, se_bitN t.black⟩

/-- `scf:base`(b), the seam in direction `e₁`: the two fine edges across the seam between `φ(t)`
and `φ(t')` both match if and only if `t, t'` match. -/
theorem seamE (t t' : Formal) :
    (MatchE (t.child true false) (t'.child false false) ∧
      MatchE (t.child true true) (t'.child false true)) ↔ MatchE t t' := by
  -- lower fine edge: thin `g₃, g₃`; thick `∂_E κ, ∂_W κ'`; black `∂_E se(ω) = ∂_E ω, ∂_W ω'`
  have h1 : MatchE (t.child true false) (t'.child false false) ↔
      t.thick.epE = t'.thick.epW ∧ t.black.bitE = t'.black.bitW := by
    rw [matchE_iff]
    change (HAtom.g3 = HAtom.g3 ∧ t.thick.epE = t'.thick.epW ∧
      (se t.black).bitE = t'.black.bitW) ↔ _
    rw [se_bitE]; simp
  -- upper fine edge: thin `g₁, g₁`; thick `∂_E F(θ) = ∂_E θ, ∂_W θ'`; black `0, 0`
  have h2 : MatchE (t.child true true) (t'.child false true) ↔ t.thin.epE = t'.thin.epW := by
    rw [matchE_iff]
    change (HAtom.g1 = HAtom.g1 ∧ (F t.thin).epE = t'.thin.epW ∧
      false = (nw t'.black).bitW) ↔ _
    rw [F_epE, nw_bitW]; simp
  rw [h1, h2, matchE_iff]
  tauto

/-- `scf:base`(b), the seam in direction `e₂`. -/
theorem seamN (t t' : Formal) :
    (MatchN (t.child false true) (t'.child false false) ∧
      MatchN (t.child true true) (t'.child true false)) ↔ MatchN t t' := by
  -- left fine edge: thin `g₂, g₂`; thick `∂_N κ, ∂_S κ'`; black `∂_N nw(ω) = ∂_N ω, ∂_S ω'`
  have h1 : MatchN (t.child false true) (t'.child false false) ↔
      t.thick.epN = t'.thick.epS ∧ t.black.bitN = t'.black.bitS := by
    rw [matchN_iff]
    change (VAtom.g2 = VAtom.g2 ∧ t.thick.epN = t'.thick.epS ∧
      (nw t.black).bitN = t'.black.bitS) ↔ _
    rw [nw_bitN]; simp
  -- right fine edge: thin `g₀, g₀`; thick `∂_N F(θ) = ∂_N θ, ∂_S θ'`; black `0, 0`
  have h2 : MatchN (t.child true true) (t'.child true false) ↔ t.thin.epN = t'.thin.epS := by
    rw [matchN_iff]
    change (VAtom.g0 = VAtom.g0 ∧ (F t.thin).epN = t'.thin.epS ∧
      false = (se t'.black).bitS) ↔ _
    rw [F_epN, se_bitS]; simp
  rw [h1, h2, matchN_iff]
  tauto

/-- `scf:base`(b): for every pattern `w` of formal triples on `U`, `φ(w)` is legal on
`2U + [0,2)²` if and only if `w` is legal on `U`. (Stated for all formal triples; the printed
statement is the case of patterns of `𝕆`.) -/
theorem legalOn_phi_iff {U : Set Plane} {w : Plane → Formal} :
    LegalOn MatchE MatchN (fine2 U) (subst2 child w) ↔ LegalOn MatchE MatchN U w :=
  legalOn_subst2_iff child child_matchE child_matchN seamE seamN

/-- `scf:base`(a): `φ(t)` is a legal pattern of tiles of `𝕆` on `[0,2)²`. -/
theorem phi_legal {t : Formal} (h : t.InO) :
    (∀ x ∈ fine2 {0}, (subst2 child (fun _ => t) x).InO) ∧
      LegalOn MatchE MatchN (fine2 {0}) (subst2 child (fun _ => t)) :=
  ⟨subst2_mem child (fun _ h' => h'.child) (fun _ _ => h),
    legalOn_phi_iff.2 ⟨fun u hu hu' => by simp_all, fun u hu hu' => by simp_all⟩⟩

/-- `scf:base`(c): `φ` is injective on formal triples: child `(0,0)` shows `κ` and `ω`, and
child `(1,1)` shows `F(θ)`. -/
theorem child_injective {t t' : Formal} (h : ∀ s1 s2, t.child s1 s2 = t'.child s1 s2) :
    t = t' := by
  obtain ⟨θ, κ, ω⟩ := t
  obtain ⟨θ', κ', ω'⟩ := t'
  have h00 := h false false
  have h11 := h true true
  simp only [child, mk.injEq, Thick.corner.injEq, true_and] at h00 h11
  rw [F_injective h11.1, h00.1, h00.2]

end Formal

/-! ## `φ'` on letters (`scf:def-phiprime`, `scf:ruler-forward`) -/

namespace Letter

/-- `scf:def-phiprime`, `scf:tab-subst` (right): the child `ς = (s₁, s₂)` of `φ'(𝔞)`: base
`φ(𝔞̄)(ς)`, column bit `1 - b₁` if `ς₁ = 0` and `0` if `ς₁ = 1`, row bit `1 - b₂` if `ς₂ = 0`
and `0` if `ς₂ = 1`. -/
def child (x : Letter) (s1 s2 : Bool) : Letter :=
  ⟨x.base.child s1 s2, if s1 then false else !x.b1, if s2 then false else !x.b2⟩

/-- `scf:ruler-forward`(a), first half: the children of a letter of `𝔸` lie in `𝔸`
(a check over the 276 letters). -/
theorem child_inA_check : (letters.all fun x => [false, true].all fun s1 =>
    [false, true].all fun s2 => decide (x.child s1 s2).InA) = true := by
  decide +kernel

theorem InA.child {x : Letter} (h : x.InA) (s1 s2 : Bool) : (x.child s1 s2).InA := by
  have h1 := List.all_eq_true.1 child_inA_check x (mem_letters.2 h)
  have h2 := List.all_eq_true.1 h1 s1 (by cases s1 <;> simp)
  exact of_decide_eq_true (List.all_eq_true.1 h2 s2 (by cases s2 <;> simp))

theorem child_matchE (x : Letter) (s2 : Bool) : MatchE (x.child false s2) (x.child true s2) :=
  matchE_iff.2 ⟨Formal.child_matchE _ _, rfl⟩

theorem child_matchN (x : Letter) (s1 : Bool) : MatchN (x.child s1 false) (x.child s1 true) :=
  matchN_iff.2 ⟨Formal.child_matchN _ _, rfl⟩

/-- `scf:ruler-forward`(b), the seam in direction `e₁`: bases as in `scf:base`(b); the lower
fine edge carries row bits `1 - b₂, 1 - b₂'`, the upper one `0, 0`. -/
theorem seamE (x y : Letter) :
    (MatchE (x.child true false) (y.child false false) ∧
      MatchE (x.child true true) (y.child false true)) ↔ MatchE x y := by
  have h := Formal.seamE x.base y.base
  simp only [matchE_iff]
  change ((x.base.child true false).MatchE (y.base.child false false) ∧ (!x.b2) = !y.b2) ∧
    ((x.base.child true true).MatchE (y.base.child false true) ∧ false = false) ↔ _
  constructor
  · rintro ⟨⟨h1, hb⟩, h2, -⟩
    exact ⟨h.1 ⟨h1, h2⟩, by simpa using hb⟩
  · rintro ⟨hm, hb⟩
    obtain ⟨h1, h2⟩ := h.2 hm
    exact ⟨⟨h1, by rw [hb]⟩, h2, rfl⟩

/-- `scf:ruler-forward`(b), the seam in direction `e₂`. -/
theorem seamN (x y : Letter) :
    (MatchN (x.child false true) (y.child false false) ∧
      MatchN (x.child true true) (y.child true false)) ↔ MatchN x y := by
  have h := Formal.seamN x.base y.base
  simp only [matchN_iff]
  change ((x.base.child false true).MatchN (y.base.child false false) ∧ (!x.b1) = !y.b1) ∧
    ((x.base.child true true).MatchN (y.base.child true false) ∧ false = false) ↔ _
  constructor
  · rintro ⟨⟨h1, hb⟩, h2, -⟩
    exact ⟨h.1 ⟨h1, h2⟩, by simpa using hb⟩
  · rintro ⟨hm, hb⟩
    obtain ⟨h1, h2⟩ := h.2 hm
    exact ⟨⟨h1, by rw [hb]⟩, h2, rfl⟩

/-- `scf:ruler-forward`(b): for every pattern `w` of letters on `U`, `φ'(w)` is legal on
`2U + [0,2)²` if and only if `w` is legal on `U`. -/
theorem legalOn_phi'_iff {U : Set Plane} {w : Plane → Letter} :
    LegalOn MatchE MatchN (fine2 U) (subst2 child w) ↔ LegalOn MatchE MatchN U w :=
  legalOn_subst2_iff child child_matchE child_matchN seamE seamN

/-- `scf:ruler-forward`(a): `φ'(𝔞)` is a legal pattern of letters of `𝔸` on `[0,2)²`. -/
theorem phi'_legal {x : Letter} (h : x.InA) :
    (∀ y ∈ fine2 {0}, (subst2 child (fun _ => x) y).InA) ∧
      LegalOn MatchE MatchN (fine2 {0}) (subst2 child (fun _ => x)) :=
  ⟨subst2_mem child (fun _ h' => h'.child) (fun _ _ => h),
    legalOn_phi'_iff.2 ⟨fun u hu hu' => by simp_all, fun u hu hu' => by simp_all⟩⟩

/-- `scf:ruler-forward`(c): `φ'` is injective: child `(0,0)` shows `κ`, `ω` and the complements
of both bits, and child `(1,1)` shows `θ`. -/
theorem child_injective {x y : Letter} (h : ∀ s1 s2, x.child s1 s2 = y.child s1 s2) : x = y := by
  obtain ⟨t, b1, b2⟩ := x
  obtain ⟨t', b1', b2'⟩ := y
  have ht : t = t' := Formal.child_injective fun s1 s2 => congrArg base (h s1 s2)
  have h00 := h false false
  simp only [child, mk.injEq, Bool.false_eq_true, ↓reduceIte, Bool.not_inj_iff] at h00
  rw [ht, h00.2.1, h00.2.2]

end Letter

/-! ## `σ = φ' ∘ φ'` and its powers (`scf:def-phiprime`, `prop:scaffold`) -/

/-- `φ'` on patterns of letters (blockwise, `scf:def-phiprime`). -/
def phi' (w : Plane → Letter) : Plane → Letter := subst2 Letter.child w

/-- `σ` on patterns: `σ(w) = φ'(φ'(w))`, blockwise with `4 × 4` blocks. -/
def sigmaPat (w : Plane → Letter) : Plane → Letter := phi' (phi' w)

/-- `scf:def-phiprime`: `σ(𝔞)(2τ + ς) = φ'(φ'(𝔞)(τ))(ς)`, a pattern on `[0,4)²`. -/
def sigma (x : Letter) : Plane → Letter := sigmaPat fun _ => x

/-- `scf:def-phiprime`: `σⁿ(𝔞)`, a pattern on `[0,4ⁿ)²` (`n`-fold blockwise `σ`). -/
def sigmaPow (n : ℕ) (x : Letter) : Plane → Letter := sigmaPat^[n] fun _ => x

/-- The remark at 06:19: `(φ')^{2n}(𝔞) = σⁿ(𝔞)` (blockwise substitution composes). -/
theorem phi'_iterate_two_mul (n : ℕ) (x : Letter) : phi'^[2 * n] (fun _ => x) = sigmaPow n x := by
  have h : sigmaPat = phi'^[2] := rfl
  rw [sigmaPow, h, ← Function.iterate_mul]

/-- The square `[0, 4ⁿ)²`. -/
def sq (n : ℕ) : Set Plane := square 0 (4 ^ n)

theorem fine2_fine2_sq (n : ℕ) : fine2 (fine2 (sq n)) = sq (n + 1) := by
  ext x
  obtain ⟨x1, x2⟩ := x
  simp only [fine2, sq, square, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, zero_add,
    pow_succ]
  generalize (4 : ℤ) ^ n = N
  push_cast
  omega

theorem sq_zero : sq 0 = {0} := by
  ext x
  obtain ⟨x1, x2⟩ := x
  simp only [sq, square, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, zero_add, pow_zero,
    Nat.cast_one, Set.mem_singleton_iff, Prod.mk_eq_zero]
  omega

/-- `prop:scaffold`(ii): for every pattern `w` of letters on `U`, `σ(w)` is legal on
`4U + [0,4)²` if and only if `w` is legal on `U`. -/
theorem legalOn_sigma_iff {U : Set Plane} {w : Plane → Letter} :
    LegalOn Letter.MatchE Letter.MatchN (fine2 (fine2 U)) (sigmaPat w) ↔
      LegalOn Letter.MatchE Letter.MatchN U w := by
  rw [sigmaPat, phi', phi', Letter.legalOn_phi'_iff, Letter.legalOn_phi'_iff]

theorem sigmaPat_mem {U : Set Plane} {w : Plane → Letter} (hw : ∀ u ∈ U, (w u).InA) :
    ∀ x ∈ fine2 (fine2 U), (sigmaPat w x).InA :=
  subst2_mem _ (fun _ h => h.child) (subst2_mem _ (fun _ h => h.child) hw)

/-- `prop:scaffold`(i): `σⁿ(𝔞)` is a legal pattern of letters of `𝔸` on `[0,4ⁿ)²`. -/
theorem sigmaPow_legal {x : Letter} (hx : x.InA) (n : ℕ) :
    (∀ y ∈ sq n, (sigmaPow n x y).InA) ∧
      LegalOn Letter.MatchE Letter.MatchN (sq n) (sigmaPow n x) := by
  induction n with
  | zero =>
    rw [sq_zero]
    exact ⟨fun _ _ => hx, fun u hu hu' => by simp_all, fun u hu hu' => by simp_all⟩
  | succ n ih =>
    simp only [sigmaPow, Function.iterate_succ_apply'] at ih ⊢
    rw [← fine2_fine2_sq]
    exact ⟨sigmaPat_mem ih.1, legalOn_sigma_iff.2 ih.2⟩

/-- `prop:scaffold`(i): `σ` is injective. -/
theorem sigma_injective {x y : Letter} (h : ∀ i ∈ sq 1, sigma x i = sigma y i) : x = y := by
  apply Letter.child_injective
  intro s1 s2
  apply Letter.child_injective
  intro s1' s2'
  have := h (fineSite (fineSite 0 s1 s2) s1' s2') (by
    rw [← fine2_fine2_sq, sq_zero, fineSite_mem, fineSite_mem]; rfl)
  simpa [sigma, sigmaPat, phi', subst2_fineSite] using this

/-- `prop:scaffold`(iv): the bits of `σ(𝔞)(i)`: the column bit is `χ₁(𝔞)` if `i₁ = 0`, `0` if
`i₁ ∈ {1, 3}` and `1` if `i₁ = 2`; the row bit likewise with `i₂`. -/
theorem sigma_bits (x : Letter) (τ1 τ2 s1 s2 : Bool) :
    (sigma x (fineSite (fineSite 0 τ1 τ2) s1 s2)).b1 =
      (if s1 then false else if τ1 then true else x.b1) ∧
    (sigma x (fineSite (fineSite 0 τ1 τ2) s1 s2)).b2 =
      (if s2 then false else if τ2 then true else x.b2) := by
  simp only [sigma, sigmaPat, phi', subst2_fineSite, Letter.child]
  cases s1 <;> cases s2 <;> cases τ1 <;> cases τ2 <;> simp

theorem mem_sq {n : ℕ} {y : Plane} :
    y ∈ sq n ↔ 0 ≤ y.1 ∧ y.1 < 4 ^ n ∧ 0 ≤ y.2 ∧ y.2 < 4 ^ n := by
  simp [sq, square]

/-- One step of `σ` on patterns: `σ(w)(4d + e) = σ(w(d))(e)` for `e ∈ [0,4)²`. -/
theorem sigmaPat_apply (w : Plane → Letter) (d e : Plane) (he : e ∈ sq 1) :
    sigmaPat w (4 * d.1 + e.1, 4 * d.2 + e.2) = sigma (w d) e := by
  obtain ⟨d1, d2⟩ := d
  obtain ⟨e1, e2⟩ := e
  rw [mem_sq] at he
  simp only [pow_one] at he
  have h1 : (4 * d1 + e1) / 2 / 2 = d1 := by omega
  have h2 : (4 * d2 + e2) / 2 / 2 = d2 := by omega
  have h3 : (4 * d1 + e1) / 2 % 2 = e1 / 2 % 2 := by omega
  have h4 : (4 * d2 + e2) / 2 % 2 = e2 / 2 % 2 := by omega
  have h5 : (4 * d1 + e1) % 2 = e1 % 2 := by omega
  have h6 : (4 * d2 + e2) % 2 = e2 % 2 := by omega
  simp only [sigma, sigmaPat, phi', subst2, h1, h2, h3, h4, h5, h6]

/-- Blockwise substitution is local: `σⁿ(w)(4ⁿ d + y) = σⁿ(w(d))(y)` for `y ∈ [0,4ⁿ)²` (the value
at a site depends only on the letter of `w` at its depth-`n` ancestor). -/
theorem iterate_sigmaPat_block (n : ℕ) (w : Plane → Letter) (d y : Plane) (hy : y ∈ sq n) :
    sigmaPat^[n] w (4 ^ n * d.1 + y.1, 4 ^ n * d.2 + y.2) = sigmaPat^[n] (fun _ => w d) y := by
  induction n generalizing w d y with
  | zero =>
    rw [sq_zero, Set.mem_singleton_iff] at hy
    subst hy
    simp
  | succ n ih =>
    obtain ⟨y1, y2⟩ := y
    rw [mem_sq] at hy
    obtain ⟨hy1, hy1', hy2, hy2'⟩ := hy
    have hN : (0 : ℤ) < 4 ^ n := by positivity
    have hN4 : (4 : ℤ) ^ (n + 1) = 4 * 4 ^ n := by rw [pow_succ]; ring
    rw [hN4] at hy1' hy2'
    -- `y = 4ⁿ e + y'` with `e ∈ [0,4)²` and `y' ∈ [0,4ⁿ)²`
    have he : ((y1 / 4 ^ n, y2 / 4 ^ n) : Plane) ∈ sq 1 := by
      rw [mem_sq, pow_one]
      exact ⟨Int.ediv_nonneg hy1 hN.le, (Int.ediv_lt_iff_lt_mul hN).2 (by linarith),
        Int.ediv_nonneg hy2 hN.le, (Int.ediv_lt_iff_lt_mul hN).2 (by linarith)⟩
    have hy' : ((y1 % 4 ^ n, y2 % 4 ^ n) : Plane) ∈ sq n := by
      rw [mem_sq]
      exact ⟨Int.emod_nonneg _ hN.ne', Int.emod_lt_of_pos _ hN, Int.emod_nonneg _ hN.ne',
        Int.emod_lt_of_pos _ hN⟩
    have hd1 := Int.mul_ediv_add_emod y1 (4 ^ n)
    have hd2 := Int.mul_ediv_add_emod y2 (4 ^ n)
    have hL : ((4 ^ (n + 1) * d.1 + (y1, y2).1, 4 ^ (n + 1) * d.2 + (y1, y2).2) : Plane) =
        (4 ^ n * (4 * d.1 + y1 / 4 ^ n) + y1 % 4 ^ n,
          4 ^ n * (4 * d.2 + y2 / 4 ^ n) + y2 % 4 ^ n) := by
      rw [hN4]; ext <;> simp only <;> linarith
    have hR : ((y1, y2) : Plane) =
        (4 ^ n * (0 + y1 / 4 ^ n) + y1 % 4 ^ n, 4 ^ n * (0 + y2 / 4 ^ n) + y2 % 4 ^ n) := by
      ext <;> simp only <;> linarith
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hL, hR]
    rw [ih (sigmaPat w) (4 * d.1 + y1 / 4 ^ n, 4 * d.2 + y2 / 4 ^ n) _ hy',
      ih (sigmaPat fun _ => w d) (0 + y1 / 4 ^ n, 0 + y2 / 4 ^ n) _ hy']
    have hS : sigmaPat w (4 * d.1 + y1 / 4 ^ n, 4 * d.2 + y2 / 4 ^ n) =
        sigmaPat (fun _ => w d) (0 + y1 / 4 ^ n, 0 + y2 / 4 ^ n) := by
      rw [sigmaPat_apply w d _ he, zero_add, zero_add]
      rfl
    rw [hS]

/-- `scf:def-phiprime`: `σ^{n+1}(𝔞)(4ⁿ d + y) = σⁿ(σ(𝔞)(d))(y)` for `y ∈ [0,4ⁿ)²` (the paper takes
`d ∈ [0,4)²`; the identity holds for every `d`). -/
theorem sigmaPow_succ_apply (n : ℕ) (x : Letter) (d y : Plane) (hy : y ∈ sq n) :
    sigmaPow (n + 1) x (4 ^ n * d.1 + y.1, 4 ^ n * d.2 + y.2) = sigmaPow n (sigma x d) y := by
  rw [sigmaPow, Function.iterate_succ_apply, iterate_sigmaPat_block n _ d y hy]
  rfl

/-- `scf:def-phiprime`, the other order: `σ^{n+1}(𝔞) = σ(σⁿ(𝔞))` blockwise. -/
theorem sigmaPow_succ' (n : ℕ) (x : Letter) : sigmaPow (n + 1) x = sigmaPat (sigmaPow n x) :=
  Function.iterate_succ_apply' _ _ _

end FNE.Scaffold
