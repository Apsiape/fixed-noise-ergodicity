/-
# §9.3: the corner lemma (`thr:corner`), kernel-checked

The paper proves `thr:corner` on the box `V_16` (side 33) by two programs. Here it is a kernel
computation (`decide +kernel`, no `native_decide`), on the smaller box `V_6` (side 13):
* `certOK_a`, …: the kernel runs the checker of `Three/CornerCheck.lean` on the generated
  certificate of `Three/CornerData.lean` (90 updates per corner, deleting the 1565 entries of
  the dependency cone of the root in a synchronous arc-consistency run);
* `corner_lemma`: every family consistent on `V_6` and contained in `𝒟_κ` has `𝒦(0) = ∅`;
* `corner_lemma_box`: the same on every box `V_r`, `r ≥ 6`, by the restriction lemma
  (`ConsistentOn.anti`); in particular on the printed box `V_16` (`corner_lemma_V16`).

**[choice] (a strengthening; planning note 1, session 5).** The printed lemma says that on
`V_16` *every* list `𝒦(v)` is empty. Its only use (`thr:corner-plane`) needs `𝒦(0) = ∅`, and
that already holds on `V_6`: `VERIFY.md` (ENGINE-C) reports 13 as the least side on which the root
is deleted, and the kernel confirms it here. So `thr:corner-plane` is proved with `z₀ + V_6`
(stronger than `z₀ + V_16`), and the printed lemma is formalized in the form it is used
(`𝒦(0) = ∅`), on `V_6` and on every larger box. The emptiness of the other lists of `V_16` is
not formalized (unused).

Kernel cost (measured, session 7): each `certOK` declaration about 1–2 s and 0.3 GB above the
import baseline (1.7 GB); the whole file about 15 s, peak about 2 GB.
-/
import FixedNoiseErgodicity.Three.CornerCheck

set_option autoImplicit false

set_option maxRecDepth 20000

namespace FNE.Three

open FNE.Scaffold

/-! ## The four certificates -/

theorem certOK_a : certOK .a = true := by decide +kernel

theorem certOK_b : certOK .b = true := by decide +kernel

theorem certOK_c : certOK .c = true := by decide +kernel

theorem certOK_d : certOK .d = true := by decide +kernel

theorem certOK_all (κ : Corner) : certOK κ = true := by
  cases κ
  exacts [certOK_a, certOK_b, certOK_c, certOK_d]

/-! ## The corner lemma -/

/-- **`thr:corner` (corner lemma), on `V_6`.** Let `κ` be a corner. Every family `𝒦` that is
consistent on the box `V_6` and contained in `𝒟_κ` has `𝒦(0) = ∅`. -/
theorem corner_lemma (κ : Corner) {K : Plane → Set Letter} (hK : ConsistentOn (box 6) K)
    (hD : ∀ v ∈ (box 6 : Set Plane), ∀ x ∈ K v, InD κ v x) : K 0 = ∅ :=
  corner_of_certOK (certOK_all κ) hK hD

/-- `thr:corner` on every box `V_r` with `r ≥ 6`: restrict to the centred sub-box `V_6`. -/
theorem corner_lemma_box (κ : Corner) {r : ℕ} (hr : 6 ≤ r) {K : Plane → Set Letter}
    (hK : ConsistentOn (box r) K) (hD : ∀ v ∈ (box r : Set Plane), ∀ x ∈ K v, InD κ v x) :
    K 0 = ∅ :=
  corner_lemma κ (hK.anti (box_mono hr)) fun v hv => hD v (box_mono hr hv)

/-- `thr:corner` on the printed box `V_16`, in the form used by `thr:corner-plane`. -/
theorem corner_lemma_V16 (κ : Corner) {K : Plane → Set Letter} (hK : ConsistentOn (box 16) K)
    (hD : ∀ v ∈ (box 16 : Set Plane), ∀ x ∈ K v, InD κ v x) : K 0 = ∅ :=
  corner_lemma_box κ (by norm_num) hK hD

end FNE.Three
