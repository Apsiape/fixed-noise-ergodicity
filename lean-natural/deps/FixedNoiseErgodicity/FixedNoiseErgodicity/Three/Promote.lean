/-
# §9.3, token level: corner pairs at every scale and the forced word

`W` is a plane-safe set of `3`-token states for `R_M` in which every state has class `γ`
(`hγ`; the component `𝒲_γ` of `thr:phase`, `classPart`).
* `thr:def-pair`: corner pairs of order `m` (`IsCornerPair`).
* The walker lists of a corner pair satisfy the hypotheses of `thr:dyadic` (`dyadicSetup_of`,
  from `thr:lists`).
* **`thr:start`** (`thr_start`): a corner pair of order `1` (a pin on a cell, a pin of thin type
  `b`, a corner pin with bit `1`, an opposite corner letter by `thr:corner-plane`).
* **`thr:promote`** (`thr_promote`): from order `m ≥ 1` to order `m + 1` (`promote_lists`).
* **`thr:word`** (`thr_word`): a corner pair of order `2n` forces `σⁿ(𝔞)` on the walker lists
  (`word_lists`).
* Corner pairs of every order `m ≥ 1` (`exists_cornerPair`), as used in §9.4.

**[choice]** "Opposite corner letters" is written with the corner letters of `𝔸`,
`(a, κ₁, A, β, β)` and `(a, κ₂, A, ¬β, ¬β)` (`cornerLetter`, as in `DyadicSetup`), and
`y₂ − y₁ ∈ 2^m ℤ²` with its quotient `w`. In `thr:word` the pin `r` is returned as a site `y_r`
with `p_r = ι(y_r)`.
-/
import FixedNoiseErgodicity.Three.Walker

set_option autoImplicit false

namespace FNE.Three

open FNE FNE.Scaffold FNE.Family FNE.TokenGame

variable {M : TuringMachine}

/-- `thr:def-pair`: a pin pair `(ι(y₁), s₁; ι(y₂), s₂)` is a *corner pair of order `m`* if
`par(ctr(s₁))` and `par(ctr(s₂))` are opposite corner letters and `y₂ − y₁ ∈ 2^m ℤ²`. -/
def IsCornerPair (W : Set (State (RM M) 3)) (γ : Plane) (m : ℕ) (P : PinPair (RM M)) : Prop :=
  IsPinPair W P ∧ ∃ y1 w : Plane, ∃ κ1 κ2 : Corner, ∃ β : Bool,
    P.p1 = iota γ y1 ∧ P.p2 = iota γ (y1 + 2 ^ m • w) ∧
      tpar (ctr P.s1) = cornerLetter κ1 β ∧ tpar (ctr P.s2) = cornerLetter κ2 (!β)

section Pairs

variable {W : Set (State (RM M) 3)} {γ : Plane} (hW : IsPlaneSafe W)
  (hγ : ∀ st ∈ W, ∀ i, cls (st.1 i) (ctr (st.2 i)) = γ)
include hW hγ

/-- The walker lists of a corner pair of order `m ≥ 1` satisfy the hypotheses of `thr:dyadic`
(`thr:lists`(c),(d)). -/
theorem dyadicSetup_of {m : ℕ} (hm : 1 ≤ m) {P : PinPair (RM M)} {y1 w : Plane}
    {κ1 κ2 : Corner} {β : Bool} (hP : IsPinPair W P) (h1 : P.p1 = iota γ y1)
    (h2 : P.p2 = iota γ (y1 + 2 ^ m • w)) (e1 : tpar (ctr P.s1) = cornerLetter κ1 β)
    (e2 : tpar (ctr P.s2) = cornerLetter κ2 (!β)) :
    DyadicSetup (indexLists W γ P) m y1 w κ1 κ2 β where
  fam := lists_family hW hP
  ac := lists_ac hW hγ
  m_pos := hm
  p1 := by rw [lists_pin1 hW hP h1, e1]
  p2 := by rw [lists_pin2 hW hP h2, e2]

/-- **`thr:promote`.** If `𝒲` has a corner pair of order `m ≥ 1`, then it has a corner pair of
order `m + 1`. -/
theorem thr_promote {m : ℕ} (hm : 1 ≤ m) {P : PinPair (RM M)} (hP : IsCornerPair W γ m P) :
    ∃ P' : PinPair (RM M), IsCornerPair W γ (m + 1) P' := by
  obtain ⟨hpin, y1, w, κ1, κ2, β, h1, h2, e1, e2⟩ := hP
  have S := dyadicSetup_of hW hγ hm hpin h1 h2 e1 e2
  obtain ⟨zr, κr, βr, hor, -, u, κ', s, hs, hpar⟩ := promote_lists S
  rcases hor with ⟨hz, hk, hb⟩ | ⟨hz, hk, hb⟩
  · -- `r = 1`: clone token `3` onto token `2`
    refine ⟨⟨P.p1, P.s1, _, s⟩, pin_clone_two hW hs, y1, u, κ1, κ', β, h1, ?_, e1, ?_⟩
    · show iota γ (y1 + 2 ^ m • (zr + 2 • u)) = iota γ (y1 + 2 ^ (m + 1) • u)
      rw [hz, zero_add, smul_smul, ← pow_succ]
    · rw [hpar, hb]
  · -- `r = 2`: clone token `3` onto token `1`
    refine ⟨⟨_, s, P.p2, P.s2⟩, pin_clone_one hW hs, y1 + 2 ^ m • (zr + 2 • u), -u, κ', κ2, β,
      rfl, ?_, ?_, e2⟩
    · rw [h2, hz, smul_add, smul_neg, smul_smul, ← pow_succ]
      congr 1
      abel
    · show tpar (ctr s) = cornerLetter κ' β
      rw [hpar, hb, Bool.not_not]

/-- **`thr:word`.** Let `n ≥ 1` and let `𝐩` be a corner pair of order `2n`. For one of its pins,
`p_r = ι(y_r)`, and a corner `κ_r`, the walker lists are the word `σⁿ(𝔞)` with
`𝔞 = (a, κ_r, A, 1, 1)`: `𝓛_𝐩(y_r + y) = {σⁿ(𝔞)(y)}` for every `y ∈ [0, 4ⁿ)²`. -/
theorem thr_word {n : ℕ} (hn : 1 ≤ n) {P : PinPair (RM M)} (hP : IsCornerPair W γ (2 * n) P) :
    ∃ yr : Plane, ∃ κr : Corner, (P.p1 = iota γ yr ∨ P.p2 = iota γ yr) ∧
      ∀ y ∈ square 0 (4 ^ n),
        indexLists W γ P (yr + y) = {sigmaPow n (cornerLetter κr true) y} := by
  obtain ⟨hpin, y1, w, κ1, κ2, β, h1, h2, e1, e2⟩ := hP
  have S := dyadicSetup_of hW hγ (by omega) hpin h1 h2 e1 e2
  obtain ⟨zr, κr, hor, hw⟩ := word_lists S
  refine ⟨y1 + 4 ^ n • zr, κr, ?_, hw⟩
  rcases hor with ⟨hz, -⟩ | ⟨hz, -⟩
  · left; rw [hz, smul_zero, add_zero]; exact h1
  · right
    rw [h2, hz, pow_mul]
    norm_num

/-- **`thr:start`.** A nonempty `𝒲` has a corner pair of order `1`. -/
theorem thr_start (hne : W.Nonempty) : ∃ P : PinPair (RM M), IsCornerPair W γ 1 P := by
  -- A pin on a cell.
  obtain ⟨st, hst⟩ := hne
  obtain ⟨s0, -, h0⟩ := walk_token hW (fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) hst 0
    trivial (iota γ 0)
  have hd0 := cloneAll_mem hW h0 0
  simp only [Function.update_self] at hd0
  have hP0 : IsPinPair W ⟨iota γ 0, s0, iota γ 0, s0⟩ := by
    refine ⟨(iota γ 0, s0), ?_⟩
    show pinState _ _ _ ∈ W
    convert hd0 using 1
    simp only [pinState]
    ext i <;> fin_cases i <;> rfl
  have hac0 := lists_ac (P := ⟨iota γ 0, s0, iota γ 0, s0⟩) hW hγ
  have hs0 := lists_pin1 (γ := γ) hW hP0 (y := 0) rfl
  obtain ⟨c, hc, -⟩ := thr_thin hac0 (z0 := 0) (θ0 := (tpar (ctr s0)).base.thin)
    (by rw [hs0]; rintro x rfl; rfl)
  -- A pin of thin type `b`.
  obtain ⟨s1, hs1⟩ := walker_total hW hP0 (iota γ (c + (1, 1)))
  have hb1 : (tpar (ctr s1)).base.thin = .b := by
    rw [hc (c + (1, 1)) _ ⟨s1, hs1, rfl⟩, add_sub_cancel_left]; rfl
  obtain ⟨θs, hθs⟩ := (tpar_inA (ctr_mem s1)).thin_b hb1
  have hP1 := pin_clone_both hW hs1
  have hL1 := lists_family (γ := γ) hW hP1
  have hac1 := lists_ac (P := ⟨iota γ (c + (1, 1)), s1, iota γ (c + (1, 1)), s1⟩) hW hγ
  have hs1' : indexLists W γ ⟨iota γ (c + (1, 1)), s1, iota γ (c + (1, 1)), s1⟩ (c + (1, 1)) =
      {bLetter θs} := by
    rw [lists_pin1 hW hP1 rfl, hθs]; rfl
  -- A corner pin with bit `1`.
  have hc' : HasThinPhase (indexLists W γ ⟨iota γ (c + (1, 1)), s1, iota γ (c + (1, 1)), s1⟩) c :=
    hasThinPhase_of hac1 c (c + (1, 1)) (by
      rw [hs1']; rintro x rfl; rw [add_sub_cancel_left]; rfl)
  have hang : angle (indexLists W γ ⟨iota γ (c + (1, 1)), s1, iota γ (c + (1, 1)), s1⟩) c 0 =
      {θs} := by
    ext θ
    simp only [angle, Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [show c + 2 • (0 : Plane) + (1, 1) = c + (1, 1) by rw [smul_zero, add_zero], hs1',
      Set.mem_singleton_iff]
    constructor
    · intro h; exact F_injective (by simpa [bLetter] using h)
    · rintro rfl; rfl
  obtain ⟨θ, hθ⟩ := thr_ne_singleton hL1 hac1 hc' hang
  have S : CoarseSetup (indexLists W γ ⟨iota γ (c + (1, 1)), s1, iota γ (c + (1, 1)), s1⟩) c θ :=
    ⟨hL1, hac1, hc', fun z => (hθ z).1⟩
  obtain ⟨zb, hzb⟩ : ∃ zb, θ zb = .b := by
    have hx := (hθ 0).2.1
    have hy := (hθ 0).2.2
    have hxy := (hθ ((0 : Plane) + (1, 0))).2.2
    rw [hx] at hxy
    cases h0 : θ 0
    · exact ⟨(0 : Plane) + (1, 0) + (0, 1), by rw [hxy, h0]; rfl⟩
    · exact ⟨0, h0⟩
    · exact ⟨(0 : Plane) + (0, 1), by rw [hy, h0]; rfl⟩
    · exact ⟨(0 : Plane) + (1, 0), by rw [hx, h0]; rfl⟩
  have hcorner : ∀ x ∈ indexLists W γ ⟨iota γ (c + (1, 1)), s1, iota γ (c + (1, 1)), s1⟩
      (c + 2 • zb), ∃ κ, x = cornerLetter κ true := by
    intro x hx
    have hxA := S.up_inA zb hx
    rw [hzb] at hxA
    obtain ⟨θ'', h''⟩ := hxA.thin_b rfl
    have hth := S.sw_thin zb hx
    obtain ⟨⟨xθ, xκ, xω⟩, b1, b2⟩ := x
    have e1 : xκ = .corner (F θ'') := congrArg (fun l : Letter => l.base.thick) h''
    have e2 : xω = .A := congrArg (fun l : Letter => l.base.black) h''
    have e3 : (!b1) = false := congrArg Letter.b1 h''
    have e4 : (!b2) = false := congrArg Letter.b2 h''
    simp only [Bool.not_eq_false'] at e3 e4
    have e0 : xθ = .a := hth
    subst e0 e1 e2 e3 e4
    exact ⟨F θ'', rfl⟩
  obtain ⟨s2, hs2⟩ := walker_total hW hP1 (iota γ (c + 2 • zb))
  obtain ⟨κ, hκ⟩ := hcorner _ ⟨s2, hs2, rfl⟩
  have hP2 := pin_clone_both hW hs2
  have hL2 := lists_family (γ := γ) hW hP2
  have hac2 := lists_ac (P := ⟨iota γ (c + 2 • zb), s2, iota γ (c + 2 • zb), s2⟩) hW hγ
  have hs2' : indexLists W γ ⟨iota γ (c + 2 • zb), s2, iota γ (c + 2 • zb), s2⟩ (c + 2 • zb) =
      {cornerLetter κ true} := by
    rw [lists_pin1 hW hP2 rfl, hκ]
  -- An opposite corner letter (`thr:corner-plane`).
  obtain ⟨⟨v1, v2⟩, -, κ', s3, hs3, hpar3⟩ := corner_plane hL2 hac2 hs2'
  have hc2 := hasThinPhase_self hac2 (by rw [hs2']; rintro x rfl; rfl)
  have hthin := hc2 _ _ ⟨s3, hs3, hpar3⟩
  rw [add_sub_cancel_left] at hthin
  have hev : v1 % 2 = 0 ∧ v2 % 2 = 0 := by
    simp only [thinRule] at hthin
    split_ifs at hthin with h1 h2 <;>
      first | exact ⟨h1, h2⟩ | exact absurd hthin (by simp [cornerLetter])
  have hv : ((v1, v2) : Plane) = 2 ^ 1 • (v1 / 2, v2 / 2) := by
    ext <;> simp only [pow_one, two_nsmul, Prod.fst_add, Prod.snd_add] <;> omega
  refine ⟨⟨iota γ (c + 2 • zb), s2, iota γ (c + 2 • zb + (v1, v2)), s3⟩,
    ⟨pin_clone_two hW hs3, c + 2 • zb, (v1 / 2, v2 / 2), κ, κ', true, rfl, ?_, hκ, hpar3⟩⟩
  show iota γ (c + 2 • zb + (v1, v2)) = _
  rw [hv]

/-- Corner pairs of every order `m ≥ 1` (`thr:start` and `thr:promote` applied `m − 1` times). -/
theorem exists_cornerPair (hne : W.Nonempty) (m : ℕ) (hm : 1 ≤ m) :
    ∃ P : PinPair (RM M), IsCornerPair W γ m P := by
  induction m, hm using Nat.le_induction with
  | base => exact thr_start hW hγ hne
  | succ m hm ih =>
    obtain ⟨P, hP⟩ := ih
    exact thr_promote hW hγ hm hP

end Pairs

end FNE.Three
