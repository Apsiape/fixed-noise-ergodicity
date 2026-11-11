/-
# Definition: the domination field (`def:domination`, Section 3.3; reused in Section 4.3)
-/
import FixedNoiseErgodicity.Basic

set_option autoImplicit false

namespace FNE

/-- `def:domination`. The domination field `E`, computed from the replacement indicators alone:
`E_0 ≡ 0`; for `t ≥ 1`, `E_t(v) = 1` if `(v, t)` is an event, and otherwise `E_t(v) = 1` iff
there are providers `i ≠ i'` and offsets `d, d' ∈ {-1,0,1}²` with
`E_{t-1}(u + d, P + c_i) = E_{t-1}(u + d', P + c_{i'}) = 1`.
Indexing as in `Noise`: `η (t, v)` is `η_{t+1}(v)`, so `domField η (t + 1) v` reads `η (t, v)`. -/
def domField {k : ℕ} (η : ℕ × Site k → Bool) : ℕ → Site k → Prop
  | 0 => fun _ => False
  | t + 1 => fun v => η (t, v) = true ∨
      ∃ i i' : Option (Fin k), i ≠ i' ∧ ∃ d ∈ box 1, ∃ d' ∈ box 1,
        domField η t (v.1 + d, v.2 + provider k i) ∧ domField η t (v.1 + d', v.2 + provider k i')

theorem domField_zero {k : ℕ} (η : ℕ × Site k → Bool) (v : Site k) : ¬ domField η 0 v :=
  fun h => h

theorem domField_succ {k : ℕ} (η : ℕ × Site k → Bool) (t : ℕ) (v : Site k) :
    domField η (t + 1) v ↔ (η (t, v) = true ∨
      ∃ i i' : Option (Fin k), i ≠ i' ∧ ∃ d ∈ box 1, ∃ d' ∈ box 1,
        domField η t (v.1 + d, v.2 + provider k i) ∧
          domField η t (v.1 + d', v.2 + provider k i')) :=
  Iff.rfl

/-- The replacement indicators of a noise realisation. -/
def Noise.flags {k : ℕ} {R : WangSet} (ω : Noise k R) : ℕ × Site k → Bool := fun p => (ω p).1

end FNE
