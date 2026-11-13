/-
# Facts read off the tables, used in §6 and §9

All are finite statements about App. A and `scf:def-ruler`, checked in the kernel (statements about
every letter of `𝔸` go through one Boolean fold over the 276 letters, `forall_letters`).
* 09:81–86: the thin maps `θ^↔`, `θ^↕` (involutions, commuting); thin types match horizontally
  exactly when `θ' = θ^↔` and vertically exactly when `θ' = θ^↕`; the same for the corners
  `F(θ)`; the four types `θ, θ^↔, θ^↕, (θ^↔)^↕` are distinct.
* 09:88: corner letters `(a, κ, A, b, b)`; the letters of thin type `b` are `(b, F(θ), A, 0, 0)`.
* (T1)–(T5) (09:89–95).
* 06:47: the red endpoints of the corners (`∠b` south-west, `∠c` south-east, `∠a` north-west,
  `∠d` north-east corner of a red rectangle).
-/
import FixedNoiseErgodicity.Scaffold.Tables

set_option autoImplicit false

set_option maxRecDepth 20000

namespace FNE.Scaffold

/-- A fact checked by one Boolean fold over the 276 letters holds for every letter of `𝔸`. -/
theorem forall_letters {p : Letter → Bool} (h : Letter.letters.all p = true) {x : Letter}
    (hx : x.InA) : p x = true :=
  List.all_eq_true.1 h x (Letter.mem_letters.2 hx)

/-! ## The thin maps (09:81–86) -/

namespace Thin

/-- 09:83: `a^↔ = c`, `c^↔ = a`, `b^↔ = d`, `d^↔ = b`. -/
def horiz : Thin → Thin
  | a => c | c => a | b => d | d => b

/-- 09:83: `a^↕ = d`, `d^↕ = a`, `b^↕ = c`, `c^↕ = b`. -/
def vert : Thin → Thin
  | a => d | d => a | b => c | c => b

theorem horiz_horiz (θ : Thin) : θ.horiz.horiz = θ := by cases θ <;> rfl

theorem vert_vert (θ : Thin) : θ.vert.vert = θ := by cases θ <;> rfl

theorem horiz_vert (θ : Thin) : θ.horiz.vert = θ.vert.horiz := by cases θ <;> rfl

/-- 09:86: thin types match horizontally, `θ` to the west, exactly when `θ' = θ^↔`. -/
theorem epE_eq_epW_iff (θ θ' : Thin) : θ.epE = θ'.epW ↔ θ' = θ.horiz := by
  cases θ <;> cases θ' <;> decide

/-- 09:86: thin types match vertically, `θ` to the south, exactly when `θ' = θ^↕`. -/
theorem epN_eq_epS_iff (θ θ' : Thin) : θ.epN = θ'.epS ↔ θ' = θ.vert := by
  cases θ <;> cases θ' <;> decide

/-- 09:86: `∂_E F(θ) = ∂_W F(θ')` exactly when `θ' = θ^↔`. -/
theorem F_epE_eq_F_epW_iff (θ θ' : Thin) : (F θ).epE = (F θ').epW ↔ θ' = θ.horiz := by
  rw [F_epE, F_epW, epE_eq_epW_iff]

/-- 09:86: `∂_N F(θ) = ∂_S F(θ')` exactly when `θ' = θ^↕`. -/
theorem F_epN_eq_F_epS_iff (θ θ' : Thin) : (F θ).epN = (F θ').epS ↔ θ' = θ.vert := by
  rw [F_epN, F_epS, epN_eq_epS_iff]

/-- 09:86: the four types `θ, θ^↔, θ^↕, (θ^↔)^↕` are distinct. -/
theorem four_distinct (θ : Thin) :
    [θ, θ.horiz, θ.vert, θ.horiz.vert].Nodup := by
  cases θ <;> decide

end Thin

/-! ## Corner letters and letters of thin type `b` (09:88) -/

/-- 09:88: a *corner letter* is a letter of thin type `a` whose thick type is a corner. -/
def Letter.IsCornerLetter (x : Letter) : Prop := x.base.thin = .a ∧ x.base.thick.IsCorner

instance : DecidablePred Letter.IsCornerLetter := fun x => by
  unfold Letter.IsCornerLetter; infer_instance

/-- 09:88: a corner letter of `𝔸` is `(a, κ, A, b, b)`. -/
theorem Letter.InA.cornerLetter {x : Letter} (hx : x.InA) (hc : x.IsCornerLetter) :
    x.base.black = .A ∧ x.b1 = x.b2 := by
  have := forall_letters (p := fun x => decide (x.IsCornerLetter → x.base.black = .A ∧
    x.b1 = x.b2)) (by decide +kernel) hx
  exact of_decide_eq_true this hc

/-- 09:88: a letter of `𝔸` of thin type `b` is `(b, F(θ), A, 0, 0)` for exactly one thin type
`θ`. -/
theorem Letter.InA.thin_b {x : Letter} (hx : x.InA) (hb : x.base.thin = .b) :
    ∃ θ, x = ⟨⟨.b, .corner (F θ), .A⟩, false, false⟩ := by
  have := forall_letters (p := fun x => decide (x.base.thin = .b →
    ∃ θ ∈ Thin.all, x = ⟨⟨.b, .corner (F θ), .A⟩, false, false⟩)) (by decide +kernel) hx
  obtain ⟨θ, -, h⟩ := of_decide_eq_true this hb
  exact ⟨θ, h⟩

/-! ## (T1)–(T5) (09:89–95) -/

/-- (T1) Every corner has exactly one red endpoint among its north and south endpoints, and
exactly one among its east and west endpoints. -/
theorem T1 (k : Corner) :
    (k.epN.IsRed ↔ ¬ k.epS.IsRed) ∧ (k.epE.IsRed ↔ ¬ k.epW.IsRed) := by
  cases k <;> decide

/-- (T2) `∂_W θ` is green exactly for `θ ∈ {a, d}`, and `∂_S θ` is green exactly for
`θ ∈ {a, c}`. -/
theorem T2 (θ : Thin) :
    (¬ θ.epW.IsRed ↔ θ = .a ∨ θ = .d) ∧ (¬ θ.epS.IsRed ↔ θ = .a ∨ θ = .c) := by
  cases θ <;> decide

/-- (T3), thin type `c`: a letter of `𝔸` of thin type `c` is a line with black `B` or `C` and
column bit `0`; black `B` excludes the vertical atom `r₀`, black `C` excludes `r₂`. -/
theorem T3_c {x : Letter} (hx : x.InA) (hc : x.base.thin = .c) :
    ¬ x.base.thick.IsCorner ∧ (x.base.black = .B ∨ x.base.black = .C) ∧ x.b1 = false ∧
      (x.base.black = .B → x.base.thick.epN ≠ .r0) ∧
      (x.base.black = .C → x.base.thick.epN ≠ .r2) := by
  have := forall_letters (p := fun x => decide (x.base.thin = .c →
    ¬ x.base.thick.IsCorner ∧ (x.base.black = .B ∨ x.base.black = .C) ∧ x.b1 = false ∧
      (x.base.black = .B → x.base.thick.epN ≠ .r0) ∧
      (x.base.black = .C → x.base.thick.epN ≠ .r2))) (by decide +kernel) hx
  exact of_decide_eq_true this hc

/-- (T3), thin type `d`: a letter of `𝔸` of thin type `d` is a line with black `D` or `E` and
row bit `0`; black `D` excludes the horizontal atom `r₃`, black `E` excludes `r₁`. -/
theorem T3_d {x : Letter} (hx : x.InA) (hd : x.base.thin = .d) :
    ¬ x.base.thick.IsCorner ∧ (x.base.black = .D ∨ x.base.black = .E) ∧ x.b2 = false ∧
      (x.base.black = .D → x.base.thick.epE ≠ .r3) ∧
      (x.base.black = .E → x.base.thick.epE ≠ .r1) := by
  have := forall_letters (p := fun x => decide (x.base.thin = .d →
    ¬ x.base.thick.IsCorner ∧ (x.base.black = .D ∨ x.base.black = .E) ∧ x.b2 = false ∧
      (x.base.black = .D → x.base.thick.epE ≠ .r3) ∧
      (x.base.black = .E → x.base.thick.epE ≠ .r1))) (by decide +kernel) hx
  exact of_decide_eq_true this hd

/-- (T3), bits: `B` and `C` have equal east and west bits, `0` and `1`; `D` and `E` have equal
north and south bits, `1` and `0`. -/
theorem T3_bits :
    Black.B.bitE = false ∧ Black.B.bitW = false ∧ Black.C.bitE = true ∧ Black.C.bitW = true ∧
    Black.D.bitN = true ∧ Black.D.bitS = true ∧ Black.E.bitN = false ∧ Black.E.bitS = false :=
  by decide

/-- (T4) By (R4), a line of a letter of `𝔸` with equal bits is not a red crossing: if one of
its atoms is red, the other is green. -/
theorem T4 {x : Letter} (hx : x.InA) {α : VAtom} {γ : HAtom}
    (hl : x.base.thick = .line α γ) (hb : x.b1 = x.b2) : ¬ (α.IsRed ∧ γ.IsRed) := by
  intro hr
  have h4 := hx.2.2.2.2
  rw [Letter.R4, hl] at h4
  exact h4 hr hb

/-- (T5) The only black type with north and east bits `0` is `A`; the black types with north
bit `1` and south bit `0` are `B` and `C`; those with east bit `1` and west bit `0` are `D` and
`E`. -/
theorem T5_black (ω : Black) :
    ((ω.bitN = false ∧ ω.bitE = false) ↔ ω = .A) ∧
    ((ω.bitN = true ∧ ω.bitS = false) ↔ ω = .B ∨ ω = .C) ∧
    ((ω.bitE = true ∧ ω.bitW = false) ↔ ω = .D ∨ ω = .E) := by
  cases ω <;> decide

/-- (T5) A letter of `𝔸` of thin type `a` with black `A` is a corner; with any other black type
it is a line. -/
theorem T5_letter {x : Letter} (hx : x.InA) (ha : x.base.thin = .a) :
    (x.base.black = .A ↔ x.base.thick.IsCorner) := by
  have := forall_letters (p := fun x => decide (x.base.thin = .a →
    (x.base.black = .A ↔ x.base.thick.IsCorner))) (by decide +kernel) hx
  exact of_decide_eq_true this ha

/-! ## Red endpoints of the corners (06:47) -/

/-- 06:47: `∠b` has red north `r₀` and red east `r₁`; `∠c` red north `r₂` and red west `r₁`;
`∠a` red south `r₀` and red east `r₃`; `∠d` red south `r₂` and red west `r₃` (and the other two
endpoints of each corner are green). -/
theorem corner_red_endpoints :
    (Corner.b.epN = .r0 ∧ Corner.b.epE = .r1 ∧ ¬ Corner.b.epS.IsRed ∧ ¬ Corner.b.epW.IsRed) ∧
    (Corner.c.epN = .r2 ∧ Corner.c.epW = .r1 ∧ ¬ Corner.c.epS.IsRed ∧ ¬ Corner.c.epE.IsRed) ∧
    (Corner.a.epS = .r0 ∧ Corner.a.epE = .r3 ∧ ¬ Corner.a.epN.IsRed ∧ ¬ Corner.a.epW.IsRed) ∧
    (Corner.d.epS = .r2 ∧ Corner.d.epW = .r3 ∧ ¬ Corner.d.epN.IsRed ∧ ¬ Corner.d.epE.IsRed) := by
  decide

/-- 06:7: every corner of `𝕆` has black type `A` (`scf:tab-alphabet`). -/
theorem corner_black_A {t : Formal} (h : t.InO) (hc : t.thick.IsCorner) : t.black = .A :=
  (h.corner hc).1

end FNE.Scaffold
