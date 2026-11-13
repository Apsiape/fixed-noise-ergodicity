/-
# Section 6.3–6.4: free coordinates, centres, `fam:positive`(b),(c) for every tiling, addresses

* 06:188–190: free coordinates `𝓕_d(m)` (`IsFree`) and centres `cen_d(m)` (`cen`); for the phase
  `1/3`, `z ∈ 𝓕_d(m)` iff `z ∈ I̊_d(m)` and `own(z) = d` (`isFree_iff_own`, 06:215); every centre
  is free (`cen_free`).
* `fam:positive`(b) for **every** tiling `ϑ` of `𝔸^r` with scaffold pairs `f_0^q`
  (`positive_b_row_all`, `positive_b_col_all`), from a routing lemma on a line
  (`carrier_iff_nearest`, the argument of `prop:routing` between the nearest walls).
* `fam:positive`(c) for every such tiling: active-or-seed iff in `𝓕_d(m) × 𝓕_d(m')`
  (`positive_c`), and every seed tile sits at a pair of centres (`seed_at_centres`; it needs only
  the scaffold pair).
* Addresses (06:368): `adr a d z = #{free ≤ z} - #{free ≤ cen}` in the frame of depth `d` containing
  `z` (one definition serves `ad` and `ad⁻`); `adr_cen` (`ad(cen) = 0`) and `adr_succ`
  (`ad(z+1) = ad(z) + [z+1 free]` inside a frame).
-/
import FixedNoiseErgodicity.Family.Positive

set_option autoImplicit false

namespace FNE.Family

open FNE.Scaffold

/-! ## Free coordinates and centres -/

/-- 06:190: the centre `cen_d(m) = a_d + (4m+2)4^d + 1`. -/
def cen (a : ℕ → ℤ) (d : ℕ) (m : ℤ) : ℤ := a d + (4 * m + 2) * 4 ^ d + 1

/-- 06:188: `z` is a *free coordinate* of `I_d(m)`: `z ∈ I̊_d(m)` and `z` lies in no frame of a
depth `1 ≤ e < d`. -/
def IsFree (a : ℕ → ℤ) (d : ℕ) (m z : ℤ) : Prop :=
  frameLo a d m < z ∧ z < frameHi a d m ∧ ∀ e < d, 1 ≤ e → ¬ InFrame a e z

instance (a : ℕ → ℤ) (d : ℕ) (m z : ℤ) : Decidable (IsFree a d m z) := by
  unfold IsFree; infer_instance

/-- 06:215: for the phase `1/3`, `z ∈ 𝓕_d(m)` iff `z ∈ I̊_d(m)` and `own(z) = d`. -/
theorem isFree_iff_own {d : ℕ} (hd : 1 ≤ d) {m z : ℤ} :
    IsFree (towerOffsets third) d m z ↔ frameLo (towerOffsets third) d m < z ∧
      z < frameHi (towerOffsets third) d m ∧ own _ forall_inFrame_third z = d := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, le_antisymm (own_le _ _ hd ⟨m, h1.le, h2.le⟩) ?_⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨ho1, ho2⟩ := own_spec _ forall_inFrame_third z
    exact h3 _ hlt ho1 ho2
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun e he he1 hin => ?_⟩
    have := own_le _ forall_inFrame_third he1 hin
    omega

/-- 06:190 (with `fam:frames`(c)): every centre is a free coordinate (it is `≡ a_e + 1` modulo
`4^{e+1}` for every `e < d`). -/
theorem cen_free {a : ℕ → ℤ} (ha : FrameOffsets a) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) :
    IsFree a d m (cen a d m) := by
  have hp : (4 : ℤ) ≤ 4 ^ d := le_self_pow₀ (by norm_num) (by omega)
  refine ⟨by simp only [frameLo, cen]; nlinarith, by simp only [frameHi, cen]; nlinarith,
    fun e hed he hin => ?_⟩
  have hdvd : (4 : ℤ) ^ (e + 1) ∣ a d - a e := by
    rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, ha.emod hed.le, Int.sub_self, Int.zero_emod]
  have hdvd' : (4 : ℤ) ^ (e + 1) ∣ 4 ^ d := pow_dvd_pow 4 hed
  have hq : (4 : ℤ) ≤ 4 ^ (e + 1) := le_self_pow₀ (by norm_num) (by omega)
  have hpe : (1 : ℤ) ≤ 4 ^ e := one_le_pow₀ (by norm_num)
  have hpe4 : (4 : ℤ) ^ (e + 1) = 4 * 4 ^ e := by ring
  have r1 : (cen a d m - a e) % 4 ^ (e + 1) = 1 := by
    refine emod_of_dvd_sub ?_ (by norm_num) (by linarith)
    have : cen a d m - a e - 1 = (a d - a e) + (4 * m + 2) * 4 ^ d := by simp only [cen]; ring
    rw [this]; exact dvd_add hdvd (Dvd.dvd.mul_left hdvd' _)
  rw [inFrame_iff, r1] at hin
  omega

/-! ## A routing lemma on a line -/

/-- `prop:routing` between the nearest walls: on a line whose walls are unbounded in both
directions, with flows obeying the flow rules and matching, a site off the walls has both flows
empty iff its nearest wall to the west is a left side and its nearest wall to the east a right
side. -/
theorem carrier_iff_nearest {W : ℤ → Option Side} (hW : ∀ n : ℤ, ∃ k : ℕ, W (n - k) ≠ none)
    (hE : ∀ n : ℤ, ∃ k : ℕ, W (n + 1 + k) ≠ none) {φW φE : ℤ → Flow}
    (hrule : ∀ x, FlowRules (W x) (φW x) (φE x)) (hmatch : ∀ x, φE x = φW (x + 1))
    {x : ℤ} (hx : W x = none) :
    (φW x = Flow.empty ∧ φE x = Flow.empty) ↔
      W (westWall W hW x) = some .lo ∧ W (eastWall W hE x) = some .hi := by
  set w1 := westWall W hW x with hw1
  set w2 := eastWall W hE x with hw2
  have hw1x : w1 < x := by
    rcases lt_or_eq_of_le (westWall_le (hW := hW) x) with h | h
    · exact h
    · exfalso
      have := westWall_spec (hW := hW) x
      rw [← hw1] at h this
      rw [h, hx] at this; exact this rfl
  have hxw2 : x < w2 := lt_eastWall (hE := hE) x
  have hmid : ∀ y, w1 < y → y < w2 → W y = none := fun y h1 h2 => by
    rcases le_or_gt y x with h | h
    · exact westWall_max h1 h
    · exact eastWall_min h h2
  have ha : ∀ y, w1 ≤ y → y < w2 → φE y = φE w1 ∧ φW (y + 1) = φE w1 := by
    intro y hy hy2
    induction y, hy using Int.leInduction with
    | base => exact ⟨rfl, (hmatch w1).symm⟩
    | succ y hy ih =>
      have ih := ih (by omega)
      have hr := hrule (y + 1)
      rw [hmid (y + 1) (by omega) hy2] at hr
      refine ⟨?_, ?_⟩
      · rw [← hr]; exact ih.2
      · rw [← hmatch (y + 1), ← hr]; exact ih.2
  have e1 := (ha x hw1x.le hxw2).1
  have e2 := (ha (x - 1) (by omega) (by omega)).2
  rw [sub_add_cancel] at e2
  have hψ : φW w2 = φE w1 := by
    have := (ha (w2 - 1) (by omega) (by omega)).2
    rwa [sub_add_cancel] at this
  obtain ⟨s1, hs1⟩ := Option.ne_none_iff_exists'.1 (westWall_spec (hW := hW) x)
  obtain ⟨s2, hs2⟩ := Option.ne_none_iff_exists'.1 (eastWall_spec (hE := hE) x)
  rw [← hw1] at hs1; rw [← hw2] at hs2
  have r1 := hrule w1
  have r2 := hrule w2
  rw [hs1] at r1; rw [hs2, hψ] at r2
  rw [e1, e2, and_self, hs1, hs2]
  generalize φE w1 = ψ at r1 r2
  obtain ⟨b1, b2⟩ := ψ
  cases s1 <;> cases s2 <;> cases b1 <;> cases b2 <;> simp_all [FlowRules, Flow.empty]

/-! ## `fam:positive`(b) and (c) for every tiling -/

section Positive

variable {f : ℕ → Plane → Letter} {ϑ : Plane → RTile}

/-- **`fam:positive`(b)**, rows, for **every** tiling `ϑ` of `𝔸^r` with scaffold pairs `f_0^q`:
`ϑ(ξ)` is a horizontal carrier iff `ξ₁ ∈ I̊_d(m)` for `d = own(ξ₂)` and some `m`. -/
theorem positive_b_row_all (hf : IsInfTower (diag third) f) (hq : ∀ ξ, (ϑ ξ).q = quarter (f 0) ξ)
    (hR : ∀ ξ, (ϑ ξ).InR) (hL : LegalOn RTile.MatchE RTile.MatchN Set.univ ϑ) (ξ : Plane) :
    (ϑ ξ).HCarrier ↔ ∃ m,
      frameLo (towerOffsets third) (own _ forall_inFrame_third ξ.2) m < ξ.1 ∧
        ξ.1 < frameHi (towerOffsets third) (own _ forall_inFrame_third ξ.2) m := by
  have hvw : ∀ x, (ϑ (x, ξ.2)).vw = rowWall f ξ.2 x := fun x => by
    simp only [RTile.vw, hq, quarter_apply, rowWall]
  have hrule : ∀ x, FlowRules (rowWall f ξ.2 x) (ϑ (x, ξ.2)).fW (ϑ (x, ξ.2)).fE := fun x => by
    rw [← hvw]; exact (hR _).2.1
  have hmatch : ∀ x, (ϑ (x, ξ.2)).fE = (ϑ (x + 1, ξ.2)).fW := fun x => by
    have := (hL.1 (x, ξ.2) trivial trivial).2
    simpa only [Prod.mk_add_mk, add_zero] using this
  obtain ⟨x, z⟩ := ξ
  simp only at hvw hrule hmatch ⊢
  unfold RTile.HCarrier
  cases hx : rowWall f z x with
  | some s =>
    have r := hrule x
    rw [hx] at r
    refine ⟨fun h => absurd h (not_carrier_of_wall r), fun ⟨m, h1, h2⟩ => ?_⟩
    rw [no_wall_inside hf h1 h2] at hx; cases hx
  | none =>
    rw [carrier_iff_nearest (rowWall_west hf z) (rowWall_east hf z) hrule hmatch hx]
    constructor
    · rintro ⟨h1, h2⟩; exact row_carrier_mp hf hx h1 h2
    · rintro ⟨m, h1, h2⟩; exact row_carrier_mpr hf h1 h2

/-- **`fam:positive`(b)**, columns, for every tiling `ϑ` of `𝔸^r` with scaffold pairs `f_0^q`. -/
theorem positive_b_col_all (hf : IsInfTower (diag third) f) (hq : ∀ ξ, (ϑ ξ).q = quarter (f 0) ξ)
    (hR : ∀ ξ, (ϑ ξ).InR) (hL : LegalOn RTile.MatchE RTile.MatchN Set.univ ϑ) (ξ : Plane) :
    (ϑ ξ).VCarrier ↔ ∃ m,
      frameLo (towerOffsets third) (own _ forall_inFrame_third ξ.1) m < ξ.2 ∧
        ξ.2 < frameHi (towerOffsets third) (own _ forall_inFrame_third ξ.1) m := by
  have hhw : ∀ y, (ϑ (ξ.1, y)).hw = colWall f ξ.1 y := fun y => by
    simp only [RTile.hw, hq, quarter_apply, colWall]
  have hrule : ∀ y, FlowRules (colWall f ξ.1 y) (ϑ (ξ.1, y)).fS (ϑ (ξ.1, y)).fN := fun y => by
    rw [← hhw]; exact (hR _).2.2
  have hmatch : ∀ y, (ϑ (ξ.1, y)).fN = (ϑ (ξ.1, y + 1)).fS := fun y => by
    have := (hL.2 (ξ.1, y) trivial trivial).2
    simpa only [Prod.mk_add_mk, add_zero] using this
  obtain ⟨x, z⟩ := ξ
  simp only at hhw hrule hmatch ⊢
  unfold RTile.VCarrier
  cases hx : colWall f x z with
  | some s =>
    have r := hrule z
    rw [hx] at r
    refine ⟨fun h => absurd h (not_carrier_of_wall r), fun ⟨m, h1, h2⟩ => ?_⟩
    rw [no_wall_inside_col hf h1 h2] at hx; cases hx
  | none =>
    rw [carrier_iff_nearest (colWall_south hf x) (colWall_north hf x) hrule hmatch hx]
    constructor
    · rintro ⟨h1, h2⟩; exact col_carrier_mp hf hx h1 h2
    · rintro ⟨m, h1, h2⟩; exact col_carrier_mpr hf h1 h2

/-- **`fam:positive`(c)**, first claim, for every tiling `ϑ` of `𝔸^r` with scaffold pairs
`f_0^q`: `ϑ(ξ)` is both a horizontal and a vertical carrier (that is, active or seed) iff
`ξ ∈ 𝓕_d(m) × 𝓕_d(m')` for some `d ≥ 1` and `m, m'`. -/
theorem positive_c (hf : IsInfTower (diag third) f) (hq : ∀ ξ, (ϑ ξ).q = quarter (f 0) ξ)
    (hR : ∀ ξ, (ϑ ξ).InR) (hL : LegalOn RTile.MatchE RTile.MatchN Set.univ ϑ) (ξ : Plane) :
    ((ϑ ξ).HCarrier ∧ (ϑ ξ).VCarrier) ↔ ∃ d m m', 1 ≤ d ∧
      IsFree (towerOffsets third) d m ξ.1 ∧ IsFree (towerOffsets third) d m' ξ.2 := by
  rw [positive_b_row_all hf hq hR hL, positive_b_col_all hf hq hR hL]
  obtain ⟨d1, hd1⟩ := own_spec _ forall_inFrame_third ξ.1
  obtain ⟨d2, hd2⟩ := own_spec _ forall_inFrame_third ξ.2
  constructor
  · rintro ⟨⟨m, h1, h2⟩, ⟨m', h3, h4⟩⟩
    have le1 := own_le _ forall_inFrame_third d2 ⟨m, h1.le, h2.le⟩
    have le2 := own_le _ forall_inFrame_third d1 ⟨m', h3.le, h4.le⟩
    have heq : own _ forall_inFrame_third ξ.1 = own _ forall_inFrame_third ξ.2 :=
      le_antisymm le1 le2
    refine ⟨own _ forall_inFrame_third ξ.1, m, m', d1, ?_, ?_⟩
    · rw [isFree_iff_own d1]; exact ⟨by rwa [heq], by rwa [heq], rfl⟩
    · rw [isFree_iff_own d1]; exact ⟨h3, h4, heq.symm⟩
  · rintro ⟨d, m, m', hd, h1, h2⟩
    rw [isFree_iff_own hd] at h1 h2
    obtain ⟨a1, a2, a3⟩ := h1
    obtain ⟨b1, b2, b3⟩ := h2
    exact ⟨⟨m, by rwa [b3], by rwa [b3]⟩, ⟨m', by rwa [a3], by rwa [a3]⟩⟩

end Positive

/-- `2^{2d} = 4^d` in `ℤ`. -/
theorem two_pow_two_mul (d : ℕ) : (2 : ℤ) ^ (2 * d) = 4 ^ d := by
  rw [pow_mul]; norm_num

/-- **`fam:positive`(c)**, second claim: every quarter `((1,1), 𝔞)` of `f_0`, with `𝔞` the
index-`0` letter with dark ruler bits, sits at a pair of centres `(cen_d(m), cen_d(m'))`,
`d ≥ 1`. (So every seed tile does.) As printed: the column has an even rank `r` (`fam:rank-bits`),
`r ≠ 0` (thin type `a`), and `fam:red` gives `s₁ = s₂ = 2^r`. -/
theorem seed_at_centres {f : ℕ → Plane → Letter} (hf : IsInfTower (diag third) f) {ξ : Plane}
    (hq : quarter (f 0) ξ = ⟨(true, true), index0Dark⟩) :
    ∃ d m m', 1 ≤ d ∧ ξ = (cen (towerOffsets third) d m, cen (towerOffsets third) d m') := by
  rw [quarter_apply] at hq
  simp only [SPair.mk.injEq] at hq
  obtain ⟨hquad, hlet⟩ := hq
  simp only [quad, Prod.mk.injEq, decide_eq_true_eq] at hquad
  obtain ⟨hξ1, hξ2⟩ := hquad
  set x := half ξ with hx
  obtain ⟨r, hr⟩ := exists_rank_third x.1
  have hr' : IsRank (col (diag third)) x.1 r := hr
  obtain ⟨-, hv, -, hS, hl⟩ := red_col (hf.towerRel (r + 2)) le_rfl hr'
  have hb := rank_bits_col (hf.towerRel (r + 1)) (Nat.lt_succ_self r) hr'
  rw [hlet] at hv hS hl hb
  -- the thick type `∠b` has red north endpoint `r₀` and no red south endpoint
  have hvb : (Thick.corner Corner.b).vRed = some .r0 := by decide
  change (Thick.corner Corner.b).vRed = _ at hv
  rw [hvb] at hv
  split_ifs at hv with hc hc1
  · -- `sres col = 2^r`; now `sres row = 2^r`
    have hrow : sres (row (diag third)) r x.2 = 2 ^ r := by
      rcases lt_or_eq_of_le hc.1 with h1 | h1
      · rcases lt_or_eq_of_le hc.2 with h2 | h2
        · exact absurd (by decide : (Thick.corner Corner.b).IsCorner) (hl h1 h2)
        · obtain ⟨k, hk, hred⟩ := hS h2
          cases hk
          exact absurd hred (by decide)
      · exact h1.symm
    -- `r` is even
    have hre : r % 2 = 0 := by
      simp only [index0Dark] at hb
      by_contra h
      have : r % 2 = 1 := by omega
      simp [this] at hb
    -- `r ≠ 0`: a child at a quadrant with `ς₁ = 1` has thin type `c` or `b`, not `a`
    have hr0 : r ≠ 0 := by
      rintro rfl
      have hch := (hf.towerRel 1).chain (m := 0) (by omega) x
      have hanc : ancP (diag third) 0 x = x := rfl
      rw [hanc, hlet] at hch
      have hd : dig (col (diag third)) 0 x.1 = true := hr.1
      rw [hd] at hch
      have := congrArg (fun y : Letter => y.base.thin) hch
      revert this
      cases dig (row (diag third)) 0 x.2 <;> simp [index0Dark, Letter.child, Formal.child]
    obtain ⟨d, rfl⟩ : ∃ d, r = 2 * d := ⟨r / 2, by omega⟩
    have hd1 : 1 ≤ d := by omega
    -- residues: `x_i - 1/3 ≡ 4^d (mod 4^{d+1})`
    have hW : wsum third (2 * d + 2) = wsum third (2 * d + 1) + 2 * 4 ^ d := by
      rw [wsum_succ_top]
      have : third (2 * d + 1) = true := by simp only [third, decide_eq_true_eq]; omega
      rw [this, two_pow_odd]; simp [bitZ]
    have hP : (2 : ℤ) ^ (2 * d + 2) = 4 * 4 ^ d := by
      rw [pow_add, two_pow_two_mul]; ring
    have key : ∀ z : ℤ, (z - wsum third (2 * d + 2)) % 2 ^ (2 * d + 2) = 2 ^ (2 * d) →
        ∀ ζ : ℤ, ζ % 2 = 1 → ζ / 2 = z → ∃ m, ζ = cen (towerOffsets third) d m := by
      intro z hz ζ hζ hζz
      rw [hW, hP, two_pow_two_mul] at hz
      have hk := Int.mul_ediv_add_emod (z - (wsum third (2 * d + 1) + 2 * 4 ^ d)) (4 * 4 ^ d)
      rw [hz] at hk
      have hζ' := Int.mul_ediv_add_emod ζ 2
      rw [hζ, hζz] at hζ'
      refine ⟨2 * ((z - (wsum third (2 * d + 1) + 2 * 4 ^ d)) / (4 * 4 ^ d)) + 1, ?_⟩
      simp only [cen, towerOffsets]
      linear_combination (-1 : ℤ) * hζ' - 2 * hk
    have hc1' : sres (col (diag third)) (2 * d) x.1 = 2 ^ (2 * d) := hc1
    obtain ⟨m, hm⟩ := key x.1 hc1' ξ.1 hξ1 rfl
    obtain ⟨m', hm'⟩ := key x.2 hrow ξ.2 hξ2 rfl
    exact ⟨d, m, m', hd1, Prod.ext hm hm'⟩
  · cases hv

/-! ## Addresses (06:368) -/

/-- The index `m` of the window `[a_d + 4m·4^d, a_d + 4(m+1)4^d)` containing `z`; the frame
`I_d(m)` lies in it. -/
def fidx (a : ℕ → ℤ) (d : ℕ) (z : ℤ) : ℤ := (z - a d) / 4 ^ (d + 1)

theorem fidx_eq {a : ℕ → ℤ} {d : ℕ} {m z : ℤ} (h1 : frameLo a d m ≤ z) (h2 : z ≤ frameHi a d m) :
    fidx a d z = m := by
  have hp : (0 : ℤ) < 4 ^ d := by positivity
  have hp4 : (4 : ℤ) ^ (d + 1) = 4 * 4 ^ d := by ring
  simp only [frameLo, frameHi] at h1 h2
  unfold fidx
  rw [hp4, show z - a d = (z - a d - 4 * 4 ^ d * m) + 4 * 4 ^ d * m by ring,
    Int.add_mul_ediv_left _ _ (by positivity), Int.ediv_eq_zero_of_lt (by nlinarith) (by nlinarith),
    zero_add]

/-- The number of free coordinates of `I_d(m)` in `(frameLo, z]`. -/
noncomputable def nfree (a : ℕ → ℤ) (d : ℕ) (m z : ℤ) : ℕ :=
  ((Finset.Ioc (frameLo a d m) z).filter (IsFree a d m)).card

/-- 06:368: the address of `z` at depth `d`: the number of free coordinates `≤ z` minus the number
of those `≤ cen_d(m)`, in the frame `I_d(m)` whose window contains `z`. On `𝓕_d(m)` it is the
increasing map onto an interval with `ad(cen) = 0`; elsewhere in `I̊_d(m)` it is `ad⁻`. -/
noncomputable def adr (a : ℕ → ℤ) (d : ℕ) (z : ℤ) : ℤ :=
  (nfree a d (fidx a d z) z : ℤ) - nfree a d (fidx a d z) (cen a d (fidx a d z))

/-- `ad(cen_d(m)) = 0`. -/
theorem adr_cen {a : ℕ → ℤ} {d : ℕ} (m : ℤ) : adr a d (cen a d m) = 0 := by
  have hp : (0 : ℤ) < 4 ^ d := by positivity
  have : fidx a d (cen a d m) = m :=
    fidx_eq (by simp only [frameLo, cen]; nlinarith) (by simp only [frameHi, cen]; nlinarith)
  simp [adr, this]

/-- 06:368: inside a frame, `ad(z + 1) = ad(z) + 1` if `z + 1` is free and `ad(z + 1) = ad(z)`
otherwise. -/
theorem adr_succ {a : ℕ → ℤ} {d : ℕ} {m z : ℤ} (h1 : frameLo a d m ≤ z) (h2 : z + 1 ≤ frameHi a d m) :
    adr a d (z + 1) = adr a d z + if IsFree a d m (z + 1) then 1 else 0 := by
  have e1 : fidx a d z = m := fidx_eq h1 (by omega)
  have e2 : fidx a d (z + 1) = m := fidx_eq (by omega) h2
  have hI : Finset.Ioc (frameLo a d m) (z + 1) = insert (z + 1) (Finset.Ioc (frameLo a d m) z) := by
    ext w; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
  have hn : z + 1 ∉ Finset.Ioc (frameLo a d m) z := by simp
  simp only [adr, e1, e2, nfree, hI, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun hm => hn (Finset.mem_of_mem_filter _ hm))]
    push_cast; ring
  · ring

end FNE.Family
