/-
# Section 6.3: frames and free coordinates; the phase `1/3`

* `fam:def-frames`: offsets with `a_{d+1} ≡ a_d (mod 4^{d+1})` (`FrameOffsets`); the offsets of a
  tower, `a_d = 2(ϖ₀ mod 2^{2d+1}) ≡ 2ϖ₀ (mod 4^{d+1})`, satisfy it.
* `fam:frames`(a), (b), (d).
* `fam:laminar`, for any family of integer intervals.
* The phase `1/3` (06:219): its digits `third`, `3 (ϖ₀ mod 2^{2d+1}) = 2·4^d + 1`, and every
  coordinate has a finite rank (`1/3 ∉ ℤ`).
* The owner depth `own(z)` (06:215).
-/
import FixedNoiseErgodicity.Family.Walls

set_option autoImplicit false

namespace FNE.Family

open FNE.Scaffold

/-! ## Frame offsets -/

/-- `fam:def-frames`: integers `a_d` with `a_{d+1} ≡ a_d (mod 4^{d+1})`. -/
def FrameOffsets (a : ℕ → ℤ) : Prop := ∀ d, a (d + 1) % 4 ^ (d + 1) = a d % 4 ^ (d + 1)

theorem FrameOffsets.emod {a : ℕ → ℤ} (ha : FrameOffsets a) {e d : ℕ} (h : e ≤ d) :
    a d % 4 ^ (e + 1) = a e % 4 ^ (e + 1) := by
  induction d, h using Nat.le_induction with
  | base => rfl
  | succ d hed ih =>
    rw [← ih, ← Int.emod_emod_of_dvd (a (d + 1)) (pow_dvd_pow 4 (by omega : e + 1 ≤ d + 1)), ha d,
      Int.emod_emod_of_dvd _ (pow_dvd_pow 4 (by omega : e + 1 ≤ d + 1))]

/-- The frame offsets of a tower with phase `(ϖ₀, ϖ₀)`: `a_d = 2 (ϖ₀ mod 2^{2d+1})`. -/
def towerOffsets (c : ℕ → Bool) (d : ℕ) : ℤ := 2 * wsum c (2 * d + 1)

theorem four_pow_eq_two_pow (d : ℕ) : (4 : ℤ) ^ (d + 1) = 2 ^ (2 * d + 1 + 1) := by
  rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf

theorem towerOffsets_spec (c : ℕ → Bool) (d : ℕ) :
    towerOffsets c d % 4 ^ (d + 1) = 2 * wsum c (2 * d + 1) % 4 ^ (d + 1) := rfl

theorem frameOffsets_tower (c : ℕ → Bool) : FrameOffsets (towerOffsets c) := by
  intro d
  simp only [towerOffsets]
  rw [four_pow_eq_two_pow, pow_succ, mul_comm (2 ^ (2 * d + 1)) 2,
    Int.mul_emod_mul_of_pos _ _ (by norm_num : (0 : ℤ) < 2),
    Int.mul_emod_mul_of_pos _ _ (by norm_num : (0 : ℤ) < 2),
    wsum_emod _ (by omega : 2 * d + 1 ≤ 2 * (d + 1) + 1), wsum_emod _ le_rfl]

/-! ## `fam:frames` -/

theorem frameLo_lt_frameHi (a : ℕ → ℤ) (d : ℕ) (m : ℤ) : frameLo a d m < frameHi a d m := by
  have : (1 : ℤ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
  simp only [frameLo, frameHi]; nlinarith

/-- `fam:frames`(a), first claim: frames of the same depth are disjoint. -/
theorem frame_window_unique {a : ℕ → ℤ} {d : ℕ} {m m' : ℤ} {z : ℤ}
    (h : frameLo a d m ≤ z ∧ z ≤ frameHi a d m) (h' : frameLo a d m' ≤ z ∧ z ≤ frameHi a d m') :
    m = m' := by
  have hp : (0 : ℤ) < 4 ^ d := by positivity
  simp only [frameLo, frameHi] at h h'
  generalize (4 : ℤ) ^ d = p at hp h h'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : m + 1 ≤ m' := hlt
    nlinarith
  · have : m' + 1 ≤ m := hlt
    nlinarith

/-- `x ≡ ρ (mod M)` when `M ∣ x - ρ` and `0 ≤ ρ < M`. -/
theorem emod_of_dvd_sub {x ρ M : ℤ} (h : M ∣ x - ρ) (h0 : 0 ≤ ρ) (h1 : ρ < M) : x % M = ρ := by
  obtain ⟨k, hk⟩ := h
  rw [show x = ρ + M * k by linarith, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]

/-- `fam:frames`(a), second claim: if `e < d`, no endpoint of a frame of depth `d` lies in a frame
of depth `e` (the endpoints are `≡ a_e + 1` and `≡ a_e (mod 4^{e+1})`). -/
theorem endpoint_not_inFrame {a : ℕ → ℤ} (ha : FrameOffsets a) {e d : ℕ} (hed : e < d) (m : ℤ) :
    ¬ InFrame a e (frameLo a d m) ∧ ¬ InFrame a e (frameHi a d m) := by
  have hdvd : (4 : ℤ) ^ (e + 1) ∣ a d - a e := by
    rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, ha.emod hed.le, Int.sub_self, Int.zero_emod]
  have hdvd' : (4 : ℤ) ^ (e + 1) ∣ 4 ^ d := pow_dvd_pow 4 hed
  have hq : (4 : ℤ) ≤ 4 ^ (e + 1) := le_self_pow₀ (by norm_num) (by omega)
  have hp : (1 : ℤ) ≤ 4 ^ e := one_le_pow₀ (by norm_num)
  have hpe : (4 : ℤ) ^ (e + 1) = 4 * 4 ^ e := by ring
  have r1 : (frameLo a d m - a e) % 4 ^ (e + 1) = 1 := by
    refine emod_of_dvd_sub ?_ (by norm_num) (by linarith)
    have : frameLo a d m - a e - 1 = (a d - a e) + (4 * m + 1) * 4 ^ d := by
      simp only [frameLo]; ring
    rw [this]; exact dvd_add hdvd (Dvd.dvd.mul_left hdvd' _)
  have r0 : (frameHi a d m - a e) % 4 ^ (e + 1) = 0 := by
    refine emod_of_dvd_sub ?_ (by norm_num) (by linarith)
    have : frameHi a d m - a e - 0 = (a d - a e) + (4 * m + 3) * 4 ^ d := by
      simp only [frameHi]; ring
    rw [this]; exact dvd_add hdvd (Dvd.dvd.mul_left hdvd' _)
  rw [inFrame_iff, inFrame_iff, r1, r0]
  constructor <;> omega

/-- **`fam:frames`(a)**: two frames of different depths `e < d` are disjoint, or the one of depth
`e` lies in the interior of the other. -/
theorem frames_nested {a : ℕ → ℤ} (ha : FrameOffsets a) {e d : ℕ} (hed : e < d) (m m' : ℤ) :
    (frameHi a e m' < frameLo a d m ∨ frameHi a d m < frameLo a e m') ∨
      (frameLo a d m < frameLo a e m' ∧ frameHi a e m' < frameHi a d m) := by
  obtain ⟨h1, h2⟩ := endpoint_not_inFrame ha hed m
  simp only [InFrame, not_exists, not_and, not_le] at h1 h2
  have h1 := h1 m'; have h2 := h2 m'
  have := frameLo_lt_frameHi a e m'; have := frameLo_lt_frameHi a d m
  by_contra hc
  push Not at hc
  omega

/-- **`fam:frames`(b)**: if `e < d`, every frame of depth `d` contains a frame of depth `e`. -/
theorem frames_contain (a : ℕ → ℤ) {e d : ℕ} (hed : e < d) (m : ℤ) :
    ∃ m', frameLo a d m ≤ frameLo a e m' ∧ frameHi a e m' ≤ frameHi a d m := by
  -- a left endpoint `p₀` of depth `e` in `[L, L + 4^{e+1})`, `L = frameLo a d m`
  have hM : (0 : ℤ) < 4 ^ (e + 1) := by positivity
  have hp1 : (1 : ℤ) ≤ 4 ^ e := one_le_pow₀ (by norm_num)
  have hMe : (4 : ℤ) ^ (e + 1) = 4 * 4 ^ e := by ring
  obtain ⟨X, hX⟩ : ∃ X, X = a e + 4 ^ e + 1 - frameLo a d m := ⟨_, rfl⟩
  have hdiv := Int.mul_ediv_add_emod X (4 ^ (e + 1))
  have hnn := Int.emod_nonneg X hM.ne'
  have hlt := Int.emod_lt_of_pos X hM
  have hp0 : IsLeftEnd a e (frameLo a d m + X % 4 ^ (e + 1)) := by
    rw [isLeftEnd_iff]
    refine emod_of_dvd_sub ⟨-(X / 4 ^ (e + 1)), by linarith⟩ (by positivity) (by linarith)
  obtain ⟨m', hm'⟩ := hp0
  refine ⟨m', ?_, ?_⟩
  · linarith
  · have he : frameHi a e m' = frameLo a e m' + 2 * 4 ^ e - 1 := by
      simp only [frameLo, frameHi]; ring
    have hd : frameHi a d m = frameLo a d m + 2 * 4 ^ d - 1 := by
      simp only [frameLo, frameHi]; ring
    have hpow : (4 : ℤ) ^ (e + 1) ≤ 4 ^ d := pow_le_pow_right₀ (by norm_num) hed
    rw [he, hd, ← hm']
    linarith

/-! ## `fam:laminar` -/

/-- `fam:laminar`, hypothesis: a family `𝒥` of integer intervals `[I.1, I.2]` with at least two
points each, any two distinct members disjoint or one in the interior of the other. -/
def Laminar (J : Set (ℤ × ℤ)) : Prop :=
  (∀ I ∈ J, I.1 < I.2) ∧ ∀ I ∈ J, ∀ I' ∈ J, I ≠ I' →
    (I.2 < I'.1 ∨ I'.2 < I.1) ∨ (I'.1 < I.1 ∧ I.2 < I'.2) ∨ (I.1 < I'.1 ∧ I'.2 < I.2)

/-- The endpoints `E` of the members of `𝒥`. -/
def endpts (J : Set (ℤ × ℤ)) : Set ℤ := {e | ∃ I ∈ J, e = I.1 ∨ e = I.2}

/-- **`fam:laminar`** (first claim): every endpoint is an endpoint of exactly one member; so it is
a left or a right endpoint, not both. -/
theorem Laminar.endpoint_unique {J : Set (ℤ × ℤ)} (hJ : Laminar J) {I I' : ℤ × ℤ} (hI : I ∈ J)
    (hI' : I' ∈ J) {e : ℤ} (he : e = I.1 ∨ e = I.2) (he' : e = I'.1 ∨ e = I'.2) : I = I' := by
  by_contra hne
  have h1 := hJ.1 I hI; have h2 := hJ.1 I' hI'
  rcases hJ.2 I hI I' hI' hne with h | h | h <;> omega

/-- **`fam:laminar`** (second claim): if `w₁ < w₂` are consecutive elements of `E`, `w₁` a left and
`w₂` a right endpoint, then `[w₁, w₂] ∈ 𝒥`. -/
theorem Laminar.mem_of_consecutive {J : Set (ℤ × ℤ)} (hJ : Laminar J) {I I' : ℤ × ℤ} (hI : I ∈ J)
    (hI' : I' ∈ J) (hlt : I.1 < I'.2) (hcons : ∀ e ∈ endpts J, ¬ (I.1 < e ∧ e < I'.2)) :
    (I.1, I'.2) ∈ J := by
  by_cases hne : I = I'
  · subst hne; exact hI
  · exfalso
    have h1 := hJ.1 I hI; have h2 := hJ.1 I' hI'
    have hI2 := hcons I.2 ⟨I, hI, Or.inr rfl⟩
    have hI'1 := hcons I'.1 ⟨I', hI', Or.inl rfl⟩
    rcases hJ.2 I hI I' hI' hne with h | h | h <;> omega

/-- **`fam:laminar`** (third claim): if a member `I` contains no other member, its endpoints are
consecutive in `E`. -/
theorem Laminar.consecutive_of_minimal {J : Set (ℤ × ℤ)} (hJ : Laminar J) {I : ℤ × ℤ} (hI : I ∈ J)
    (hmin : ∀ I' ∈ J, I' ≠ I → ¬ (I.1 ≤ I'.1 ∧ I'.2 ≤ I.2)) :
    ∀ e ∈ endpts J, ¬ (I.1 < e ∧ e < I.2) := by
  rintro e ⟨I', hI', he⟩ ⟨h1, h2⟩
  have hne : I' ≠ I := by rintro rfl; omega
  have := hmin I' hI' hne
  have := hJ.1 I' hI'
  rcases hJ.2 I' hI' I hI hne with h | h | h <;> omega

/-! ## The phase `1/3` (06:219) -/

/-- The 2-adic digits of `1/3 = 1 + 2 + 8 + 32 + ⋯`: digit `1` at `m = 0` and at odd `m`. -/
def third (m : ℕ) : Bool := decide (m = 0 ∨ m % 2 = 1)

/-- `1/3 mod 2^{2d+1} = (2·4^d + 1)/3`. -/
theorem three_wsum_third (d : ℕ) : 3 * wsum third (2 * d + 1) = 2 * 4 ^ d + 1 := by
  induction d with
  | zero => simp [wsum, third, bitZ]
  | succ d ih =>
    have e : 2 * (d + 1) + 1 = 2 * d + 1 + 1 + 1 := by ring
    rw [e, wsum_succ_top, wsum_succ_top]
    have h1 : third (2 * d + 1) = true := by simp only [third, decide_eq_true_eq]; omega
    have h2 : third (2 * d + 1 + 1) = false := by simp only [third, decide_eq_false_iff_not]; omega
    rw [h1, h2, pow_succ (4 : ℤ)]
    simp only [bitZ, ↓reduceIte, Bool.false_eq_true]
    have : (2 : ℤ) ^ (2 * d + 1) = 2 * 4 ^ d := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, pow_succ]; ring
    linarith

theorem two_pow_odd (d : ℕ) : (2 : ℤ) ^ (2 * d + 1) = 2 * 4 ^ d := by
  rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, pow_succ]; ring

/-- `third` are the digits of `1/3`: `3 (ϖ₀ mod 2^l) ≡ 1 (mod 2^l)` for every `l`. -/
theorem three_wsum_third_emod (l : ℕ) : 3 * wsum third l % 2 ^ l = 1 % 2 ^ l := by
  obtain ⟨d, hd | hd⟩ : ∃ d, l = 2 * d + 1 ∨ l = 2 * d + 1 + 1 ∨ l = 0 := by
    rcases Nat.even_or_odd l with ⟨k, hk⟩ | ⟨k, hk⟩
    · rcases k with _ | k
      · exact ⟨0, Or.inr (Or.inr (by omega))⟩
      · exact ⟨k, Or.inr (Or.inl (by omega))⟩
    · exact ⟨k, Or.inl (by omega)⟩
  · subst hd
    rw [three_wsum_third, ← two_pow_odd,
      show (2 : ℤ) ^ (2 * d + 1) + 1 = 1 + 2 ^ (2 * d + 1) * 1 by ring, Int.add_mul_emod_self_left]
  · rcases hd with hd | hd
    · subst hd
      have h := three_wsum_third d
      have h4 := two_pow_odd d
      have ht : third (2 * d + 1) = true := by simp only [third, decide_eq_true_eq]; omega
      rw [wsum_succ_top, ht,
        show 3 * (wsum third (2 * d + 1) + 2 ^ (2 * d + 1) * bitZ true) =
          1 + 2 ^ (2 * d + 1 + 1) * 2 by
          simp only [bitZ, ↓reduceIte]; rw [pow_succ (2 : ℤ) (2 * d + 1)]; linarith,
        Int.add_mul_emod_self_left]
    · subst hd; simp [wsum]

/-- The frame offsets of the phase `(1/3, 1/3)`: `a_d = (4^{d+1} + 2)/3`, that is
`3 a_d = 4^{d+1} + 2` (`a_d ≡ 2/3 (mod 4^{d+1})`). -/
theorem three_towerOffsets_third (d : ℕ) : 3 * towerOffsets third d = 4 ^ (d + 1) + 2 := by
  simp only [towerOffsets]
  have := three_wsum_third d
  rw [pow_succ]; linarith

/-- **`fam:frames`(d)**, for the phase `1/3`: with `a_d ≡ 2/3 (mod 4^{d+1})`, every integer lies
in the interior of some frame (of every large enough depth). -/
theorem exists_interior_third (z : ℤ) :
    ∃ d m, 1 ≤ d ∧ frameLo (towerOffsets third) d m < z ∧ z < frameHi (towerOffsets third) d m := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, 3 * |z| + 1 < (4 : ℤ) ^ (d + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 * |z| + 1) (by norm_num : (1 : ℤ) < 4)
    exact ⟨n, lt_of_lt_of_le hn (pow_le_pow_right₀ (by norm_num) (by omega))⟩
  -- the frame `I_{d+1}(-1) = [a - 3q + 1, a - q]`, with `q = 4^{d+1}` and `3a = 4q + 2`
  have ha := three_towerOffsets_third (d + 1)
  have hq4 : (4 : ℤ) ^ (d + 1 + 1) = 4 * 4 ^ (d + 1) := by ring
  rw [hq4] at ha
  refine ⟨d + 1, -1, by omega, ?_, ?_⟩ <;> simp only [frameLo, frameHi]
  · have := neg_abs_le z; have := abs_nonneg z; linarith
  · have := le_abs_self z; linarith

/-! ## Owner depth (06:215) -/

instance (a : ℕ → ℤ) (d : ℕ) : DecidablePred (InFrame a d) := fun z =>
  decidable_of_iff _ (inFrame_iff a d z).symm

/-- 06:215: the *owner depth* `own(z)`: the least `d ≥ 1` such that `z` lies in a frame of depth
`d` (when every integer lies in a frame). -/
noncomputable def own (a : ℕ → ℤ) (h : ∀ z, ∃ d, 1 ≤ d ∧ InFrame a d z) (z : ℤ) : ℕ :=
  Nat.find (h z)

theorem own_spec (a : ℕ → ℤ) (h : ∀ z, ∃ d, 1 ≤ d ∧ InFrame a d z) (z : ℤ) :
    1 ≤ own a h z ∧ InFrame a (own a h z) z :=
  Nat.find_spec (h z)

theorem own_le (a : ℕ → ℤ) (h : ∀ z, ∃ d, 1 ≤ d ∧ InFrame a d z) {z : ℤ} {d : ℕ} (hd : 1 ≤ d)
    (hz : InFrame a d z) : own a h z ≤ d :=
  Nat.find_min' (h z) ⟨hd, hz⟩

/-- 06:37 and 06:219: `1/3 ∉ ℤ`, so for the phase `1/3` every coordinate has a finite rank (the
2-adic valuation of `z - 1/3`). -/
theorem exists_rank_third (z : ℤ) : ∃ r, IsRank third z r := by
  have hex : ∃ m, dig third m z = true := by
    by_contra hall
    push Not at hall
    obtain ⟨d, hd⟩ : ∃ d : ℕ, |3 * z - 1| < (2 : ℤ) ^ (2 * d + 1) := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (|3 * z - 1|) (by norm_num : (1 : ℤ) < 2)
      exact ⟨n, lt_of_lt_of_le hn (pow_le_pow_right₀ (by norm_num) (by omega))⟩
    have h0 : wsum (fun m => dig third m z) (2 * d + 1) = 0 := by
      rw [wsum_congr (b' := fun _ => false) (fun m _ => by simpa using hall m), wsum_false]
    have h1 := emod_eq_wsum_dig third (2 * d + 1) z
    rw [h0] at h1
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h1
    have h2 := three_wsum_third d
    have h4 := two_pow_odd d
    have hP : (0 : ℤ) < 2 ^ (2 * d + 1) := by positivity
    have e : 3 * z - 1 = 2 ^ (2 * d + 1) * (3 * k + 1) := by linarith
    rw [e, abs_lt] at hd
    rcases (by omega : 1 ≤ 3 * k + 1 ∨ 3 * k + 1 ≤ -2) with hj | hj <;> nlinarith
  classical
  exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm => by simpa using Nat.find_min hex hm⟩

/-- The phase `(1/3, 1/3)`: every integer lies in a frame (`fam:frames`(d)), so the owner depth is
defined. -/
theorem forall_inFrame_third (z : ℤ) : ∃ d, 1 ≤ d ∧ InFrame (towerOffsets third) d z := by
  obtain ⟨d, m, hd, h1, h2⟩ := exists_interior_third z
  exact ⟨d, hd, m, h1.le, h2.le⟩

end FNE.Family
