/-
# §9.3, the corner lemma: the literal tables of the certificate, checked

The generated file `Three/CornerData.lean` stores the colour-class masks (`clsN`, …), the masks
of the lists `𝒟_κ(v)` (`dMaskA`, …) and the indices of the roots (`rootIdx`) as literals. Here
each literal is checked against its definition by a kernel evaluation (`decide +kernel`, no
`native_decide`), one declaration per table (each about a second, well under 1 GB):
* `clsN_eq`, …: `clsN = [classMask .N 0, …, classMask .N 63]`, and the same for `E`, `S`, `W`;
* `dMask_eq`: `dMask θ` is the mask of the letters of `𝔸` of thin type `θ` that are not corner
  letters with bit `0` (`dPred`);
* `letterAt_rootIdx`: the letter of index `rootIdx κ` is the root `(a, κ, A, 1, 1)`.
-/
import FixedNoiseErgodicity.Scaffold.Format
import FixedNoiseErgodicity.Scaffold.Facts
import FixedNoiseErgodicity.Three.CornerData

set_option autoImplicit false

set_option maxRecDepth 20000

namespace FNE.Three

open FNE.Scaffold

/-! ## The letters named in the corner lemma -/

/-- 09:88: the corner letter `(a, κ, A, b, b)` with bit `b`. -/
def cornerLetter (κ : Corner) (b : Bool) : Letter := ⟨⟨.a, .corner κ, .A⟩, b, b⟩

theorem cornerLetter_inA (κ : Corner) (b : Bool) : (cornerLetter κ b).InA := by
  cases κ <;> cases b <;> decide

theorem cornerLetter_isCornerLetter (κ : Corner) (b : Bool) :
    (cornerLetter κ b).IsCornerLetter :=
  ⟨rfl, trivial⟩

theorem cornerLetter_injective {κ κ' : Corner} {b b' : Bool}
    (h : cornerLetter κ b = cornerLetter κ' b') : κ = κ' ∧ b = b' := by
  simp only [cornerLetter, Letter.mk.injEq, Formal.mk.injEq, Thick.corner.injEq] at h
  exact ⟨h.1.2.1, h.2.1⟩

/-- A corner letter of `𝔸` (09:88) is `cornerLetter κ b` for its thick type `κ` and its bit `b`. -/
theorem Letter.InA.eq_cornerLetter {x : Letter} (hx : x.InA) (hc : x.IsCornerLetter) :
    ∃ κ, x = cornerLetter κ x.b1 := by
  obtain ⟨hA, hb⟩ := hx.cornerLetter hc
  obtain ⟨⟨θ, κ, ω⟩, b1, b2⟩ := x
  obtain ⟨hθ, hκ⟩ := hc
  simp only at hθ hA hb hκ ⊢
  cases κ with
  | line _ _ => exact hκ.elim
  | corner k => subst hθ hA hb; exact ⟨k, rfl⟩

/-- The test "`x` is one of the four corner letters with bit `0`", as a Boolean. -/
def zeroCornerB (x : Letter) : Bool := Corner.all.any fun κ => x == cornerLetter κ false

theorem zeroCornerB_iff (x : Letter) : zeroCornerB x = true ↔ ∃ κ, x = cornerLetter κ false := by
  simp only [zeroCornerB, List.any_eq_true, beq_iff_eq]
  exact ⟨fun ⟨κ, _, h⟩ => ⟨κ, h⟩, fun ⟨κ, h⟩ => ⟨κ, Corner.mem_all κ, h⟩⟩

/-- The letters of `𝒟_κ(v)`, `v ≠ 0`, of thin type `θ`: thin type `θ` and not a corner letter
with bit `0` (membership in `𝔸` comes from `letterMask`). -/
def dPred (θ : Thin) (x : Letter) : Bool := x.base.thin == θ && !zeroCornerB x

/-- The literal masks by thin type. -/
def dMask : Thin → ℕ
  | .a => dMaskA | .b => dMaskB | .c => dMaskC | .d => dMaskD

/-! ## The checks -/

theorem clsN_eq : clsN = (List.range 64).map (classMask .N) := by decide +kernel

theorem clsE_eq : clsE = (List.range 64).map (classMask .E) := by decide +kernel

theorem clsS_eq : clsS = (List.range 64).map (classMask .S) := by decide +kernel

theorem clsW_eq : clsW = (List.range 64).map (classMask .W) := by decide +kernel

theorem dMaskA_eq : dMaskA = letterMask (dPred .a) := by decide +kernel

theorem dMaskB_eq : dMaskB = letterMask (dPred .b) := by decide +kernel

theorem dMaskC_eq : dMaskC = letterMask (dPred .c) := by decide +kernel

theorem dMaskD_eq : dMaskD = letterMask (dPred .d) := by decide +kernel

theorem dMask_eq (θ : Thin) : dMask θ = letterMask (dPred θ) := by
  cases θ
  exacts [dMaskA_eq, dMaskB_eq, dMaskC_eq, dMaskD_eq]

theorem rootIdx_lt (κ : Corner) : rootIdx κ < 276 := by cases κ <;> decide

theorem letterAt_rootIdx (κ : Corner) :
    letterAt ⟨rootIdx κ, rootIdx_lt κ⟩ = cornerLetter κ true := by
  cases κ <;> decide +kernel

end FNE.Three
