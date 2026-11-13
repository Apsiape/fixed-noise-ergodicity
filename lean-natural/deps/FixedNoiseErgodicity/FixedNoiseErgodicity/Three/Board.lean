/-
# §6.5: the initialized board in every word (`prop:board`), hence (Q5), hence `thm:three`

Let `n ≥ 2`, `𝔞 ∈ 𝔸` and `W = σⁿ(𝔞)`. As printed, the proof uses the tower
`f_m = (φ')^{2n−m}(𝔞)` of height `2n` with all digits `0` (`wordTower`), and the frames with
offsets `a_d = 0` (`a0`): `J = I_{n−1}(0)`, `𝓕 = 𝓕_{n−1}(0)` (`BFree`, `boardF`),
`2Δ_n + 1 = cen_{n−1}(0)`.
* Walls in the board (`word_vwall`, `word_hwall`): `fam:walls` applies to every quarter of `J × J`,
  since an index coordinate in `[2^{2n−3}, 3·2^{2n−3}]` has rank `≤ 2n − 2` (`exists_rank_zero`).
* Endpoints in `J` (`leftEnd_in_J`, `rightEnd_in_J`): a frame endpoint in `J` has depth `≤ n − 1`,
  and of depth `n − 1` only the endpoints of `J` itself.
* **`prop:board`(c)**, along a line (`line_nowall`, `line_corridor`; used for rows and columns).
* **`prop:board`(a)**, the part (Q5) uses: `2Δ_n + 1 ∈ 𝓕` and at least `2ⁿ − 1` elements of `𝓕`
  are `≥ 2Δ_n + 1` (`many_free`, from the residues `resSet` of `fam:frames`(c)).
* **`prop:board`(b)** (`word_seed`).
* **(Q5)** (`board`) and **`thm:three`** (`three_tokens`).

**[choice]** `prop:board`(a) is proved in the form (Q5)(a) uses (`2Δ_n + 1 ∈ 𝓕`, at least
`2ⁿ − 1` free coordinates `≥ 2Δ_n + 1`, via `2^{d+1}` allowed residues, `card_resSet`); the exact
counts `|𝓕| = 2^{n+1} − 2` and `2ⁿ − 1` below the centre (`fam:frames`(c)) are not formalized
(unused). `prop:board`(d) is not stated separately: its content for the walker is
`WordSetup.roles_h`/`roles_v` (`thr:roles`). Part (c) is proved with `fam:frames`(a),(b) directly,
in place of `fam:laminar` (the same argument, specialized to one line).
-/
import FixedNoiseErgodicity.Three.Final

set_option autoImplicit false

namespace FNE.Three

open FNE FNE.Scaffold FNE.Family

/-! ## Frames of the phase `0` -/

/-- The frame offsets of the phase `0`: `a_d = 0`. -/
def a0 : ℕ → ℤ := fun _ => 0

theorem frameOffsets_a0 : FrameOffsets a0 := fun _ => rfl

theorem a0_spec (d : ℕ) :
    a0 d % 4 ^ (d + 1) = 2 * wsum (fun _ => false) (2 * d + 1) % 4 ^ (d + 1) := by
  simp [a0, wsum_false]

variable {n : ℕ}

theorem bD_ge (hn : 2 ≤ n) : 4 ≤ bD n := by
  unfold bD
  calc (4 : ℤ) = 4 ^ 1 := by norm_num
    _ ≤ 4 ^ (n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)

theorem frameLo_J (n : ℕ) : frameLo a0 (n - 1) 0 = bD n + 1 := by simp [frameLo, a0, bD]

theorem frameHi_J (n : ℕ) : frameHi a0 (n - 1) 0 = 3 * bD n := by simp [frameHi, a0, bD]

theorem inFrame_J {w : ℤ} (hw : InJ n w) : InFrame a0 (n - 1) w :=
  ⟨0, by rw [frameLo_J]; exact hw.1, by rw [frameHi_J]; exact hw.2⟩

theorem leftEnd_J : IsLeftEnd a0 (n - 1) (bD n + 1) := ⟨0, (frameLo_J n).symm⟩

theorem rightEnd_J : IsRightEnd a0 (n - 1) (3 * bD n) := ⟨0, (frameHi_J n).symm⟩

theorem IsLeftEnd.inFrame' {a : ℕ → ℤ} {d : ℕ} {z : ℤ} (h : IsLeftEnd a d z) : InFrame a d z := by
  obtain ⟨m, rfl⟩ := h; exact ⟨m, le_rfl, (frameLo_lt_frameHi a d m).le⟩

theorem IsRightEnd.inFrame' {a : ℕ → ℤ} {d : ℕ} {z : ℤ} (h : IsRightEnd a d z) :
    InFrame a d z := by
  obtain ⟨m, rfl⟩ := h; exact ⟨m, (frameLo_lt_frameHi a d m).le, le_rfl⟩

theorem four_pow_ge_of_ge {d : ℕ} (hn : 1 ≤ n) (hd : n ≤ d) : 4 * bD n ≤ (4 : ℤ) ^ d := by
  rw [← four_pow_eq_bD hn]; exact pow_le_pow_right₀ (by norm_num) hd

/-- A left endpoint in `J` has depth `≤ n − 1`; of depth `n − 1` it is the left endpoint of `J`. -/
theorem leftEnd_in_J (hn : 2 ≤ n) {d : ℕ} {z : ℤ} (hz : InJ n z) (h : IsLeftEnd a0 d z) :
    d ≤ n - 1 ∧ (d = n - 1 → z = bD n + 1) := by
  obtain ⟨m, rfl⟩ := h
  simp only [frameLo, a0, zero_add, InJ] at hz ⊢
  have hΔ := bD_ge hn
  constructor
  · by_contra hd
    have hK := four_pow_ge_of_ge (n := n) (d := d) (by omega) (by omega)
    generalize (4 : ℤ) ^ d = K at hz hK
    rcases le_or_gt 0 m with hm | hm
    · nlinarith [mul_nonneg hm (show (0 : ℤ) ≤ K by linarith)]
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ -m - 1 by linarith) (show (0 : ℤ) ≤ K by linarith)]
  · intro hd
    subst hd
    change (4 * m + 1) * bD n + 1 = bD n + 1
    change bD n + 1 ≤ (4 * m + 1) * bD n + 1 ∧ (4 * m + 1) * bD n + 1 ≤ 3 * bD n at hz
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ -m - 1 by linarith) (show (0 : ℤ) ≤ bD n by linarith)]
    · ring
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ m - 1 by linarith) (show (0 : ℤ) ≤ bD n by linarith)]

/-- A right endpoint in `J` has depth `≤ n − 1`; of depth `n − 1` it is the right endpoint of
`J`. -/
theorem rightEnd_in_J (hn : 2 ≤ n) {d : ℕ} {z : ℤ} (hz : InJ n z) (h : IsRightEnd a0 d z) :
    d ≤ n - 1 ∧ (d = n - 1 → z = 3 * bD n) := by
  obtain ⟨m, rfl⟩ := h
  simp only [frameHi, a0, zero_add, InJ] at hz ⊢
  have hΔ := bD_ge hn
  constructor
  · by_contra hd
    have hK := four_pow_ge_of_ge (n := n) (d := d) (by omega) (by omega)
    generalize (4 : ℤ) ^ d = K at hz hK
    rcases le_or_gt 0 m with hm | hm
    · nlinarith [mul_nonneg hm (show (0 : ℤ) ≤ K by linarith)]
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ -m - 1 by linarith) (show (0 : ℤ) ≤ K by linarith)]
  · intro hd
    subst hd
    change (4 * m + 3) * bD n = 3 * bD n
    change bD n + 1 ≤ (4 * m + 3) * bD n ∧ (4 * m + 3) * bD n ≤ 3 * bD n at hz
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ -m - 1 by linarith) (show (0 : ℤ) ≤ bD n by linarith)]
    · ring
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ m - 1 by linarith) (show (0 : ℤ) ≤ bD n by linarith)]

/-- `z ∈ 𝓕`: `z ∈ 𝓕_{n−1}(0)` for the offsets `a_d = 0`, that is `z ∈ J°` in no frame of a depth
`1 ≤ e ≤ n − 2`. -/
def BFree (n : ℕ) (z : ℤ) : Prop := IsFree a0 (n - 1) 0 z

theorem BFree.inJo {z : ℤ} (h : BFree n z) : InJo n z := by
  obtain ⟨h1, h2, -⟩ := h
  rw [frameLo_J] at h1; rw [frameHi_J] at h2
  unfold InJo; omega

theorem BFree.not_inFrame {z : ℤ} (h : BFree n z) {e : ℕ} (he : 1 ≤ e) (hen : e < n - 1) :
    ¬ InFrame a0 e z := h.2.2 e hen he

theorem bFree_of {z : ℤ} (hz : InJo n z) (h : ∀ e, 1 ≤ e → e < n - 1 → ¬ InFrame a0 e z) :
    BFree n z := by
  refine ⟨?_, ?_, fun e he1 he2 => h e he2 he1⟩
  · rw [frameLo_J]; unfold InJo at hz; omega
  · rw [frameHi_J]; unfold InJo at hz; omega

/-- A coordinate of `J°` that is not free lies in a frame of a depth `1 ≤ e ≤ n − 2`. -/
theorem exists_low_frame {z : ℤ} (hz : InJo n z) (h : ¬ BFree n z) :
    ∃ e, 1 ≤ e ∧ e < n - 1 ∧ InFrame a0 e z := by
  by_contra hc
  push Not at hc
  exact h (bFree_of hz fun e h1 h2 => hc e h1 h2)

/-! ## Ranks, the tower of the word, walls in the board -/

/-- With phase `0`, a coordinate `0 < z < 2^L` has a rank `r < L` (its `2`-adic valuation). -/
theorem exists_rank_zero {z : ℤ} (hz : 0 < z) {L : ℕ} (hL : z < 2 ^ L) :
    ∃ r, r < L ∧ IsRank (fun _ => false) z r := by
  classical
  have hle : ∀ k, L ≤ k → z % 2 ^ k = z := fun k hk =>
    Int.emod_eq_of_lt hz.le (lt_of_lt_of_le hL (pow_le_pow_right₀ (by norm_num) hk))
  have hex : ∃ r, z % 2 ^ (r + 1) ≠ 0 := ⟨L, by rw [hle _ (by omega)]; omega⟩
  set r := Nat.find hex with hr
  have h1 : z % 2 ^ (r + 1) ≠ 0 := Nat.find_spec hex
  have h0 : z % 2 ^ r = 0 := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h]; simp
    · have := Nat.find_min hex (show r - 1 < r by omega)
      rw [show r - 1 + 1 = r by omega] at this
      simpa using this
  have hrL : r < L := by
    by_contra hc
    rw [hle r (by omega)] at h0
    omega
  refine ⟨r, hrL, isRank_of_emod (l := r + 1) le_rfl ?_⟩
  rw [wsum_false, sub_zero]
  have hq : (0 : ℤ) < 2 ^ r := by positivity
  have e2 : (2 : ℤ) ^ (r + 1) = 2 * 2 ^ r := by ring
  rw [e2] at h1 ⊢
  have hmod : z % (2 * 2 ^ r) % 2 ^ r = 0 := by
    rw [Int.emod_emod_of_dvd _ (dvd_mul_left _ _)]; exact h0
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hmod
  have hnn := Int.emod_nonneg z (show (2 * 2 ^ r : ℤ) ≠ 0 by positivity)
  have hlt := Int.emod_lt_of_pos z (show (0 : ℤ) < 2 * 2 ^ r by positivity)
  generalize z % (2 * 2 ^ r) = y at *
  generalize (2 : ℤ) ^ r = q at *
  subst hk
  have hk0 : 0 ≤ k := by nlinarith
  have hk2 : k < 2 := by nlinarith
  interval_cases k <;> simp_all

/-- The tower `f_m = (φ')^{2n−m}(𝔞)` of height `2n`, with all digits `0` (prop:board, proof). -/
def wordTower (n : ℕ) (x : Letter) (m : ℕ) : Plane → Letter := phi'^[2 * n - m] fun _ => x

theorem subAt_zero (g : Plane → Letter) : subAt (false, false) g = phi' g := by
  funext v; simp [subAt, shiftBy, bitZ, phi']

theorem wordTower_rel (n : ℕ) (x : Letter) :
    TowerRel (diag fun _ => false) (wordTower n x) (2 * n) := by
  intro m hm
  simp only [wordTower, diag]
  rw [subAt_zero, show 2 * n - m = (2 * n - (m + 1)) + 1 by omega, Function.iterate_succ_apply']

theorem wordTower_zero (n : ℕ) (x : Letter) : wordTower n x 0 = sigmaPow n x := by
  rw [wordTower, Nat.sub_zero, phi'_iterate_two_mul]

/-- The values of `σⁿ(𝔞)` are letters of `𝔸`. -/
theorem sigmaPow_inA {x : Letter} (hx : x.InA) (n : ℕ) (v : Plane) : (sigmaPow n x v).InA := by
  rw [← phi'_iterate_two_mul]
  generalize 2 * n = k
  induction k generalizing v with
  | zero => exact hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact (ih _).child _ _

theorem two_pow_board (hn : 2 ≤ n) : (2 : ℤ) ^ (2 * n - 1) = 2 * bD n := by
  rw [show 2 * n - 1 = 2 * (n - 1) + 1 by omega, two_pow_odd]; rfl

/-- An index coordinate of the board is positive and below `2^{2n−1}`. -/
theorem half_bounds (hn : 2 ≤ n) {z : ℤ} (hz : InJ n z) : 0 < z / 2 ∧ z / 2 < 2 ^ (2 * n - 1) := by
  rw [two_pow_board hn]
  have := bD_ge hn
  unfold InJ at hz; omega

/-- Light vertical walls in the board (`fam:walls`, rank `≤ 2n − 2`): for `z ∈ J`, the quarter of
`W` at `(z, w)` lies on a light vertical wall with side `side` iff `z` is a left (right) endpoint
of a frame of some depth `d ≥ 1` and `w` lies in a frame of depth `d`. -/
theorem word_vwall (hn : 2 ≤ n) (x : Letter) {z : ℤ} (hz : InJ n z) (w : ℤ) (side : Family.Side) :
    vwq (sigmaPow n x) (z, w) = some side ↔ ∃ d, 1 ≤ d ∧
      ((side = .lo ∧ IsLeftEnd a0 d z) ∨ (side = .hi ∧ IsRightEnd a0 d z)) ∧ InFrame a0 d w := by
  obtain ⟨h0, h1⟩ := half_bounds hn hz
  obtain ⟨r, hr, hrank⟩ := exists_rank_zero h0 h1
  have := walls_col (wordTower_rel n x) a0_spec (ξ := (z, w)) hrank (by omega) side
  rwa [wordTower_zero] at this

/-- Light horizontal walls in the board: for `w ∈ J`, the quarter at `(z, w)` lies on a light
horizontal wall with side `side` iff `w` is a left (bottom side) or right (top side) endpoint of a
frame of some depth `d ≥ 1` and `z` lies in a frame of depth `d`. -/
theorem word_hwall (hn : 2 ≤ n) (x : Letter) (z : ℤ) {w : ℤ} (hw : InJ n w) (side : Family.Side) :
    hwq (sigmaPow n x) (z, w) = some side ↔ ∃ d, 1 ≤ d ∧
      ((side = .lo ∧ IsLeftEnd a0 d w) ∨ (side = .hi ∧ IsRightEnd a0 d w)) ∧ InFrame a0 d z := by
  obtain ⟨h0, h1⟩ := half_bounds hn hw
  obtain ⟨r, hr, hrank⟩ := exists_rank_zero h0 h1
  have := walls_row (wordTower_rel n x) a0_spec (ξ := (z, w)) hrank (by omega) side
  rwa [wordTower_zero] at this

/-! ## `prop:board`(c) along one line -/

section Line

variable {V : ℤ → Option Family.Side} {w x : ℤ}

/-- The walls along a line of the board: at `z ∈ J`, a wall of side `side` iff `z` is a
left/right endpoint of a frame of depth `d ≥ 1` such that the cross coordinate `w` lies in a frame
of depth `d`. -/
def LineWalls (n : ℕ) (V : ℤ → Option Family.Side) (w : ℤ) : Prop :=
  ∀ z, InJ n z → ∀ side, V z = some side ↔ ∃ d, 1 ≤ d ∧
    ((side = .lo ∧ IsLeftEnd a0 d z) ∨ (side = .hi ∧ IsRightEnd a0 d z)) ∧ InFrame a0 d w

theorem lineWalls_lo (hn : 2 ≤ n) (hV : LineWalls n V w) (hw : InJ n w) : V (bD n + 1) = some .lo :=
  (hV _ (show InJ n (bD n + 1) by unfold InJ; have := bD_pos n; omega) _).2
    ⟨n - 1, by omega, Or.inl ⟨rfl, leftEnd_J⟩, inFrame_J hw⟩

theorem lineWalls_hi (hn : 2 ≤ n) (hV : LineWalls n V w) (hw : InJ n w) : V (3 * bD n) = some .hi :=
  (hV _ (show InJ n (3 * bD n) by unfold InJ; have := bD_pos n; omega) _).2
    ⟨n - 1, by omega, Or.inr ⟨rfl, rightEnd_J⟩, inFrame_J hw⟩

/-- A wall at `z ∈ J` comes from a frame of depth `≤ n − 1`; of depth `n − 1` only at the
endpoints of `J`. -/
theorem lineWalls_depth (hn : 2 ≤ n) (hV : LineWalls n V w) {z : ℤ} (hz : InJ n z)
    {side : Family.Side} (h : V z = some side) :
    ∃ d, 1 ≤ d ∧ d ≤ n - 1 ∧ ((side = .lo ∧ IsLeftEnd a0 d z) ∨ (side = .hi ∧ IsRightEnd a0 d z)) ∧
      InFrame a0 d w ∧ (d = n - 1 → (side = .lo ∧ z = bD n + 1) ∨ (side = .hi ∧ z = 3 * bD n)) := by
  obtain ⟨d, hd, hend, hin⟩ := (hV z hz side).1 h
  rcases hend with ⟨hs, hl⟩ | ⟨hs, hr⟩
  · obtain ⟨h1, h2⟩ := leftEnd_in_J hn hz hl
    exact ⟨d, hd, h1, Or.inl ⟨hs, hl⟩, hin, fun e => Or.inl ⟨hs, h2 e⟩⟩
  · obtain ⟨h1, h2⟩ := rightEnd_in_J hn hz hr
    exact ⟨d, hd, h1, Or.inr ⟨hs, hr⟩, hin, fun e => Or.inr ⟨hs, h2 e⟩⟩

/-- **`prop:board`(c)**, no wall: the quarter at a point of `Z_W` lies on no light wall (along the
line). -/
theorem line_nowall (hn : 2 ≤ n) (hV : LineWalls n V w) (hx : InJo n x)
    (hfree : BFree n x ∨ BFree n w) : V x = none := by
  by_contra h
  obtain ⟨side, hs⟩ := Option.ne_none_iff_exists'.1 h
  obtain ⟨d, hd, hdn, hend, hin, htop⟩ := lineWalls_depth hn hV hx.inJ hs
  unfold InJo at hx
  rcases eq_or_lt_of_le hdn with rfl | hlt
  · rcases htop rfl with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  · rcases hfree with hf | hf
    · exact hf.not_inFrame hd hlt (by
        rcases hend with ⟨-, hl⟩ | ⟨-, hr⟩
        exacts [IsLeftEnd.inFrame' hl, IsRightEnd.inFrame' hr])
    · exact hf.not_inFrame hd hlt hin

/-- **`prop:board`(c)**, the corridor along a line: for `x ∈ J°` with `x` or the cross
coordinate `w` free, the nearest walls `x + m` to the right and `x − m'` to the left lie in `J`,
and they are a left side and a right side, in this order, iff `w ∈ 𝓕`. -/
theorem line_corridor (hn : 2 ≤ n) (hV : LineWalls n V w) (hx : InJo n x) (hw : InJo n w)
    (hfree : BFree n x ∨ BFree n w) :
    ∃ m m' : ℕ, 0 < m ∧ 0 < m' ∧ InJ n (x + m) ∧ InJ n (x - m') ∧
      V (x + m) ≠ none ∧ V (x - m') ≠ none ∧
      (∀ k : ℕ, 0 < k → k < m → V (x + k) = none) ∧
      (∀ k : ℕ, 0 < k → k < m' → V (x - k) = none) ∧
      (V (x - m') = some .lo ∧ V (x + m) = some .hi ↔ BFree n w) := by
  classical
  have hΔ := bD_ge hn
  have hx0 := hx
  unfold InJo at hx0
  have hwJ := hw.inJ
  -- the nearest wall to the right
  have hexR : ∃ k : ℕ, 0 < k ∧ V (x + k) ≠ none :=
    ⟨(3 * bD n - x).toNat, by omega, by
      rw [show x + ((3 * bD n - x).toNat : ℤ) = 3 * bD n by omega, lineWalls_hi hn hV hwJ]; simp⟩
  have hexL : ∃ k : ℕ, 0 < k ∧ V (x - k) ≠ none :=
    ⟨(x - (bD n + 1)).toNat, by omega, by
      rw [show x - ((x - (bD n + 1)).toNat : ℤ) = bD n + 1 by omega, lineWalls_lo hn hV hwJ]; simp⟩
  set m := Nat.find hexR with hm
  set m' := Nat.find hexL with hm'
  obtain ⟨hm0, hmV⟩ := Nat.find_spec hexR
  obtain ⟨hm0', hmV'⟩ := Nat.find_spec hexL
  have hmle : m ≤ (3 * bD n - x).toNat := Nat.find_min' hexR ⟨by omega, by
      rw [show x + ((3 * bD n - x).toNat : ℤ) = 3 * bD n by omega, lineWalls_hi hn hV hwJ]; simp⟩
  have hmle' : m' ≤ (x - (bD n + 1)).toNat := Nat.find_min' hexL ⟨by omega, by
      rw [show x - ((x - (bD n + 1)).toNat : ℤ) = bD n + 1 by omega, lineWalls_lo hn hV hwJ]; simp⟩
  have hJR : InJ n (x + m) := by unfold InJ; omega
  have hJL : InJ n (x - m') := by unfold InJ; omega
  have hminR : ∀ k : ℕ, 0 < k → k < m → V (x + k) = none := fun k hk hkm => by
    have := Nat.find_min hexR hkm
    push Not at this
    exact this hk
  have hminL : ∀ k : ℕ, 0 < k → k < m' → V (x - k) = none := fun k hk hkm => by
    have := Nat.find_min hexL hkm
    push Not at this
    exact this hk
  -- every point strictly between the two walls, other than `x`, carries no wall
  have hbetween : ∀ z, x - m' < z → z < x + m → z ≠ x → V z = none := by
    intro z h1 h2 h3
    rcases lt_or_gt_of_ne h3 with h | h
    · have := hminL (x - z).toNat (by omega) (by omega)
      rwa [show x - ((x - z).toNat : ℤ) = z by omega] at this
    · have := hminR (z - x).toNat (by omega) (by omega)
      rwa [show x + ((z - x).toNat : ℤ) = z by omega] at this
  have hxnw := line_nowall hn hV hx hfree
  refine ⟨m, m', hm0, hm0', hJR, hJL, hmV, hmV', hminR, hminL, ?_⟩
  constructor
  · -- if the walls are a left and a right side, then `w` is free
    rintro ⟨hlo, hhi⟩
    by_contra hwf
    have hxf : BFree n x := hfree.resolve_right hwf
    obtain ⟨e, he1, hen, hine⟩ := exists_low_frame hw hwf
    -- the left wall is the left endpoint of `J`
    have hL : x - m' = bD n + 1 := by
      obtain ⟨d, hd, hdn, hend, hin, htop⟩ := lineWalls_depth hn hV hJL hlo
      rcases eq_or_lt_of_le hdn with hdeq | hlt
      · rcases htop hdeq with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · cases h
      · exfalso
        rcases hend with ⟨-, ⟨k, hk⟩⟩ | ⟨h, -⟩
        · -- the frame `[x − m', R]` of depth `d < n − 1`
          have hR : IsRightEnd a0 d (frameHi a0 d k) := ⟨k, rfl⟩
          have hlt' := frameLo_lt_frameHi a0 d k
          by_cases hRx : x ≤ frameHi a0 d k
          · exact hxf.not_inFrame hd hlt ⟨k, by omega, hRx⟩
          · have hRJ : InJ n (frameHi a0 d k) := by unfold InJ at hJL ⊢; omega
            have := (hV _ hRJ .hi).2 ⟨d, hd, Or.inr ⟨rfl, hR⟩, hin⟩
            rw [hbetween _ (by omega) (by omega) (by omega)] at this
            cases this
        · cases h
    -- the right wall is the right endpoint of `J`
    have hR : x + m = 3 * bD n := by
      obtain ⟨d, hd, hdn, hend, hin, htop⟩ := lineWalls_depth hn hV hJR hhi
      rcases eq_or_lt_of_le hdn with hdeq | hlt
      · rcases htop hdeq with ⟨h, -⟩ | ⟨-, h⟩
        · cases h
        · exact h
      · exfalso
        rcases hend with ⟨h, -⟩ | ⟨-, ⟨k, hk⟩⟩
        · cases h
        · have hLe : IsLeftEnd a0 d (frameLo a0 d k) := ⟨k, rfl⟩
          have hlt' := frameLo_lt_frameHi a0 d k
          by_cases hLx : frameLo a0 d k ≤ x
          · exact hxf.not_inFrame hd hlt ⟨k, hLx, by omega⟩
          · have hLJ : InJ n (frameLo a0 d k) := by unfold InJ at hJR ⊢; omega
            have := (hV _ hLJ .lo).2 ⟨d, hd, Or.inl ⟨rfl, hLe⟩, hin⟩
            rw [hbetween _ (by omega) (by omega) (by omega)] at this
            cases this
    -- a frame of depth `e` inside `J` has its left endpoint strictly inside, a wall
    obtain ⟨k, hk1, hk2⟩ := frames_contain a0 (show e < n - 1 from hen) 0
    rw [frameLo_J] at hk1
    rw [frameHi_J] at hk2
    have hlt' := frameLo_lt_frameHi a0 e k
    have hne1 : frameLo a0 e k ≠ bD n + 1 := by
      intro h
      have := (endpoint_not_inFrame frameOffsets_a0 hen 0).1
      rw [frameLo_J, ← h] at this
      exact this ⟨k, le_rfl, hlt'.le⟩
    have hneX : frameLo a0 e k ≠ x := fun h => hxf.not_inFrame he1 hen ⟨k, h.le, by omega⟩
    have hLJ : InJ n (frameLo a0 e k) := by unfold InJ; omega
    have := (hV _ hLJ .lo).2 ⟨e, he1, Or.inl ⟨rfl, ⟨k, rfl⟩⟩, hine⟩
    rw [hbetween _ (by omega) (by omega) hneX] at this
    cases this
  · -- if `w` is free, the only walls of the line in `J` are the endpoints of `J`
    intro hwf
    have only : ∀ z, InJ n z → ∀ side, V z = some side →
        (side = .lo ∧ z = bD n + 1) ∨ (side = .hi ∧ z = 3 * bD n) := by
      intro z hz side hs
      obtain ⟨d, hd, hdn, -, hin, htop⟩ := lineWalls_depth hn hV hz hs
      rcases eq_or_lt_of_le hdn with hdeq | hlt
      · exact htop hdeq
      · exact absurd hin (hwf.not_inFrame hd hlt)
    obtain ⟨s1, hs1⟩ := Option.ne_none_iff_exists'.1 hmV'
    obtain ⟨s2, hs2⟩ := Option.ne_none_iff_exists'.1 hmV
    refine ⟨?_, ?_⟩
    · rcases only _ hJL _ hs1 with ⟨rfl, -⟩ | ⟨-, h⟩
      · exact hs1
      · omega
    · rcases only _ hJR _ hs2 with ⟨-, h⟩ | ⟨rfl, -⟩
      · omega
      · exact hs2

end Line

/-! ## `prop:board`(a): many free coordinates above the centre -/

/-- The residues `s ∈ [0, 4^{k+1})` in no frame interval of a depth `1 ≤ e ≤ k` (mod `4^{e+1}`),
built as in the proof of `fam:frames`(c): `{0,1,2,3}`, then
`S ∪ {4^{k+1}} ∪ (3·4^{k+1} + (S ∖ {0}))`. -/
def resSet : ℕ → Finset ℤ
  | 0 => {0, 1, 2, 3}
  | k + 1 => resSet k ∪ {4 ^ (k + 1)} ∪ ((resSet k).erase 0).image (· + 3 * 4 ^ (k + 1))

/-- `s` lies in no interval `[4^e + 1, 3·4^e]` modulo `4^{e+1}` for `1 ≤ e ≤ k`. -/
def Allowed (k : ℕ) (s : ℤ) : Prop :=
  ∀ e, 1 ≤ e → e ≤ k → ¬ (4 ^ e + 1 ≤ s % 4 ^ (e + 1) ∧ s % 4 ^ (e + 1) ≤ 3 * 4 ^ e)

theorem zero_mem_resSet (k : ℕ) : (0 : ℤ) ∈ resSet k := by
  induction k with
  | zero => simp [resSet]
  | succ k ih => simp [resSet, ih]

theorem resSet_spec (k : ℕ) : ∀ s ∈ resSet k, 0 ≤ s ∧ s < 4 ^ (k + 1) ∧ Allowed k s := by
  induction k with
  | zero =>
    intro s hs
    simp only [resSet, Finset.mem_insert, Finset.mem_singleton] at hs
    refine ⟨by omega, by norm_num; omega, fun e h1 h2 => absurd h2 (by omega)⟩
  | succ k ih =>
    intro s hs
    have hp : (0 : ℤ) < 4 ^ (k + 1) := by positivity
    have hp2 : (4 : ℤ) ^ (k + 1 + 1) = 4 * 4 ^ (k + 1) := by ring
    simp only [resSet, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_erase] at hs
    rcases hs with (hs | rfl) | ⟨t, ⟨ht0, ht⟩, rfl⟩
    · obtain ⟨h0, h1, h2⟩ := ih s hs
      refine ⟨h0, by rw [hp2]; omega, fun e he1 he2 => ?_⟩
      rcases eq_or_lt_of_le he2 with rfl | hlt
      · rw [Int.emod_eq_of_lt h0 (by rw [hp2]; omega)]; omega
      · exact h2 e he1 (by omega)
    · refine ⟨hp.le, by rw [hp2]; omega, fun e he1 he2 => ?_⟩
      rcases eq_or_lt_of_le he2 with rfl | hlt
      · rw [Int.emod_eq_of_lt hp.le (by rw [hp2]; omega)]; omega
      · have hd : (4 : ℤ) ^ (e + 1) ∣ 4 ^ (k + 1) := pow_dvd_pow 4 (by omega)
        rw [Int.emod_eq_zero_of_dvd hd]
        have : (0 : ℤ) < 4 ^ e := by positivity
        omega
    · obtain ⟨h0, h1, h2⟩ := ih t ht
      refine ⟨by omega, by rw [hp2]; omega, fun e he1 he2 => ?_⟩
      rcases eq_or_lt_of_le he2 with rfl | hlt
      · rw [Int.emod_eq_of_lt (by omega) (by rw [hp2]; omega)]; omega
      · have hd : (4 : ℤ) ^ (e + 1) ∣ 3 * 4 ^ (k + 1) :=
          Dvd.dvd.mul_left (pow_dvd_pow 4 (by omega)) 3
        rw [Int.add_emod, Int.emod_eq_zero_of_dvd hd, add_zero, Int.emod_emod_of_dvd _ dvd_rfl]
        exact h2 e he1 (by omega)

/-- `fam:frames`(c), the count: `|S_k| = 2^{k+2}`. -/
theorem card_resSet (k : ℕ) : (resSet k).card = 2 ^ (k + 2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp : (0 : ℤ) < 4 ^ (k + 1) := by positivity
    have hspec := resSet_spec k
    have hinj : Function.Injective (· + 3 * (4 : ℤ) ^ (k + 1)) := fun a b h => by simpa using h
    rw [resSet, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
      Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem (zero_mem_resSet k), ih,
      Finset.card_singleton]
    · have : 1 ≤ 2 ^ (k + 2) := Nat.one_le_two_pow
      rw [pow_succ 2 (k + 2)]; omega
    · rw [Finset.disjoint_singleton_right]
      intro h; have := (hspec _ h).2.1; omega
    · rw [Finset.disjoint_left]
      intro s hs hs'
      simp only [Finset.mem_image, Finset.mem_erase] at hs'
      obtain ⟨t, ⟨ht0, ht⟩, rfl⟩ := hs'
      have h1 := hspec t ht
      rcases Finset.mem_union.1 hs with hs | hs
      · have := (hspec _ hs).2.1; omega
      · rw [Finset.mem_singleton] at hs; omega

open Classical in
/-- The free coordinates `𝓕` of the board, as a finite set. -/
noncomputable def boardF (n : ℕ) : Finset ℤ :=
  (Finset.Icc (bD n + 2) (3 * bD n - 1)).filter (BFree n)

theorem mem_boardF {z : ℤ} : z ∈ boardF n ↔ BFree n z := by
  classical
  simp only [boardF, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨And.right, fun h => ⟨by have := h.inJo; unfold InJo at this; omega, h⟩⟩

/-- A residue `s ≠ 0` of depth `n − 1` gives the free coordinate `2Δ_n + s ≥ 2Δ_n + 1`. -/
theorem bFree_two_bD_add (hn : 2 ≤ n) {s : ℤ} (hs : s ∈ resSet (n - 2)) :
    BFree n (2 * bD n + s) := by
  obtain ⟨h0, h1, h2⟩ := resSet_spec _ s hs
  have hb : (4 : ℤ) ^ (n - 2 + 1) = bD n := by unfold bD; rw [show n - 2 + 1 = n - 1 by omega]
  rw [hb] at h1
  have hΔ := bD_ge hn
  refine bFree_of (by unfold InJo; omega) fun e he1 he2 => ?_
  rw [inFrame_iff]
  simp only [a0, sub_zero]
  have hd : (4 : ℤ) ^ (e + 1) ∣ 2 * bD n := Dvd.dvd.mul_left (by
    unfold bD; exact pow_dvd_pow 4 (by omega)) 2
  rw [Int.add_emod, Int.emod_eq_zero_of_dvd hd, zero_add, Int.emod_emod_of_dvd _ dvd_rfl]
  exact h2 e he1 (by omega)

/-- **`prop:board`(a)**, as used: at least `2ⁿ − 1` free coordinates are `≥ 2Δ_n + 1`. -/
theorem many_free (hn : 2 ≤ n) :
    2 ^ n - 1 ≤ ((boardF n).filter fun z => 2 * bD n + 1 ≤ z).card := by
  classical
  have hsub : ((resSet (n - 2)).erase 0).image (2 * bD n + ·) ⊆
      (boardF n).filter fun z => 2 * bD n + 1 ≤ z := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_erase] at hz
    obtain ⟨s, ⟨hs0, hs⟩, rfl⟩ := hz
    have := (resSet_spec _ s hs).1
    exact Finset.mem_filter.2 ⟨mem_boardF.2 (bFree_two_bD_add hn hs), by omega⟩
  have hinj : Function.Injective (2 * bD n + · : ℤ → ℤ) := fun a b h => by simpa using h
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem (zero_mem_resSet _),
    card_resSet, show n - 2 + 2 = n by omega] at hc
  exact hc

/-! ## `prop:board`(b): the seed quarter -/

theorem corner_b_of {k : Corner} (hN : k.epN.IsRed) (hE : k.epE.IsRed) : k = .b := by
  revert hN hE; cases k <;> decide

theorem bD_eq_two_pow (hn : 2 ≤ n) : bD n = 2 ^ (2 * n - 2) := by
  unfold bD
  rw [show 2 * n - 2 = 2 * (n - 1) by omega, pow_mul]; norm_num

/-- **`prop:board`(b).** The quarter of `W` at `(2Δ_n + 1, 2Δ_n + 1)` is `((1,1), 𝔟)` with `𝔟` the
index-`0` letter with dark ruler bits. -/
theorem word_seed (hn : 2 ≤ n) {x : Letter} (hx : x.InA) :
    quarter (sigmaPow n x) (2 * bD n + 1, 2 * bD n + 1) = ⟨(true, true), index0Dark⟩ := by
  have hΔ := bD_ge hn
  rw [quarter_apply]
  have hq : quad (2 * bD n + 1, 2 * bD n + 1) = (true, true) := by
    simp only [quad, Prod.mk.injEq, decide_eq_true_eq]; omega
  have hh : half (2 * bD n + 1, 2 * bD n + 1) = (bD n, bD n) := by
    simp only [half, Prod.mk.injEq]; omega
  rw [hq, hh]
  congr 1
  rw [← wordTower_zero]
  have hf := wordTower_rel n x
  have hpow := bD_eq_two_pow hn
  have hrank : IsRank (fun _ => false) (bD n) (2 * n - 2) := by
    apply isRank_of_emod (l := 2 * n - 2 + 1) le_rfl
    rw [wsum_false, sub_zero, hpow]
    exact Int.emod_eq_of_lt (by positivity) (pow_lt_pow_right₀ (by norm_num) (by omega))
  have hr2 : 2 * n - 2 + 2 ≤ 2 * n := by omega
  have hs : sres (fun _ => false) (2 * n - 2) (bD n) = 2 ^ (2 * n - 2) := by
    unfold sres
    rw [wsum_false, sub_zero, hpow]
    exact Int.emod_eq_of_lt (by positivity) (pow_lt_pow_right₀ (by norm_num) (by omega))
  obtain ⟨-, -, hN, -, -⟩ := red_col hf hr2 (x := (bD n, bD n)) hrank
  obtain ⟨-, -, hE, -, -⟩ := red_row hf hr2 (x := (bD n, bD n)) hrank
  obtain ⟨k, hk, hkN⟩ := hN hs
  obtain ⟨k', hk', hkE⟩ := hE hs
  rw [hk] at hk'
  cases hk'
  have hkb := corner_b_of hkN hkE
  have hb1 := rank_bits_col hf (by omega) (x := (bD n, bD n)) hrank
  have hb2 := rank_bits_row hf (by omega) (x := (bD n, bD n)) hrank
  have heven : (2 * n - 2) % 2 = 0 := by omega
  have hthin : (wordTower n x 0 (bD n, bD n)).base.thin = .a := by
    have hc := hf.chain (by omega : 0 < 2 * n) (bD n, bD n)
    have hd : dig (col (diag fun _ => false)) 0 (bD n) = false := by
      have h2 : bD n % 2 = 0 := by
        unfold bD
        obtain ⟨j, hj⟩ : ∃ j, n - 1 = j + 1 := ⟨n - 2, by omega⟩
        rw [hj, pow_succ]; omega
      simp [dig, anc, col, diag, bitZ, h2]
    have hd' : dig (row (diag fun _ => false)) 0 (bD n) = false := hd
    have e : wordTower n x 0 (bD n, bD n) = wordTower n x 0 (ancP (diag fun _ => false) 0 (bD n, bD n)) :=
      rfl
    rw [e, hc, hd, hd']
    rfl
  have hA : (wordTower n x 0 (bD n, bD n)).InA := by rw [wordTower_zero]; exact sigmaPow_inA hx n _
  have hblack := (hA.cornerLetter ⟨hthin, by rw [hk]; trivial⟩).1
  generalize wordTower n x 0 (bD n, bD n) = L at hk hb1 hb2 hthin hblack ⊢
  obtain ⟨⟨θ, κ, ω⟩, b1, b2⟩ := L
  simp only at hk hb1 hb2 hthin hblack
  subst hk hkb hthin hblack
  simp only [heven] at hb1 hb2
  simp only [hb1, hb2, index0Dark]
  rfl

/-! ## (Q5) and `thm:three` -/

/-- **(Q5)** (from `prop:board`): every word `σⁿ(𝔞)`, `n ≥ 2`, carries the initialized board
with the free coordinates `𝓕 = 𝓕_{n−1}(0)`. -/
theorem board (hn : 2 ≤ n) {x : Letter} (hx : x.InA) : IsBoard n (sigmaPow n x) (boardF n) where
  sub z hz := (mem_boardF.1 hz).inJo
  cen := by
    refine mem_boardF.2 ?_
    have := cen_free frameOffsets_a0 (show 1 ≤ n - 1 by omega) 0
    convert this using 1
    simp [BFree, cen, a0, bD]
  many := many_free hn
  seed := word_seed hn hx
  nowall ξ hξ := by
    have hz : (InJo n ξ.1 ∧ InJo n ξ.2) ∧ (BFree n ξ.1 ∨ BFree n ξ.2) := by
      rcases hξ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨⟨(mem_boardF.1 h1).inJo, h2⟩, Or.inl (mem_boardF.1 h1)⟩
      · exact ⟨⟨h1, (mem_boardF.1 h2).inJo⟩, Or.inr (mem_boardF.1 h2)⟩
    obtain ⟨⟨h1, h2⟩, hfree⟩ := hz
    refine ⟨?_, ?_⟩
    · exact line_nowall (V := fun z => vwq (sigmaPow n x) (z, ξ.2)) hn
        (fun z hz side => word_vwall hn x hz ξ.2 side) h1 hfree
    · exact line_nowall (V := fun z => hwq (sigmaPow n x) (ξ.1, z)) hn
        (fun z hz side => word_hwall hn x ξ.1 hz side) h2 hfree.symm
  row ξ hξ := by
    have hz : (InJo n ξ.1 ∧ InJo n ξ.2) ∧ (BFree n ξ.1 ∨ BFree n ξ.2) := by
      rcases hξ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨⟨(mem_boardF.1 h1).inJo, h2⟩, Or.inl (mem_boardF.1 h1)⟩
      · exact ⟨⟨h1, (mem_boardF.1 h2).inJo⟩, Or.inr (mem_boardF.1 h2)⟩
    obtain ⟨⟨h1, h2⟩, hfree⟩ := hz
    obtain ⟨m, m', a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ :=
      line_corridor (V := fun z => vwq (sigmaPow n x) (z, ξ.2)) hn
        (fun z hz side => word_vwall hn x hz ξ.2 side) h1 h2 hfree
    exact ⟨m, m', a1, a2, a3, a4, a5, a6, a7, a8, by rw [mem_boardF]; exact a9⟩
  col ξ hξ := by
    have hz : (InJo n ξ.1 ∧ InJo n ξ.2) ∧ (BFree n ξ.1 ∨ BFree n ξ.2) := by
      rcases hξ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨⟨(mem_boardF.1 h1).inJo, h2⟩, Or.inl (mem_boardF.1 h1)⟩
      · exact ⟨⟨h1, (mem_boardF.1 h2).inJo⟩, Or.inr (mem_boardF.1 h2)⟩
    obtain ⟨⟨h1, h2⟩, hfree⟩ := hz
    obtain ⟨m, m', a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ :=
      line_corridor (V := fun z => hwq (sigmaPow n x) (ξ.1, z)) hn
        (fun z hz side => word_hwall hn x ξ.1 hz side) h2 h1 hfree.symm
    exact ⟨m, m', a1, a2, a3, a4, a5, a6, a7, a8, by rw [mem_boardF]; exact a9⟩

/-- **`thm:three`.** If the machine `M` halts, then `R_M` is `3`-token refutable. -/
theorem three_tokens (M : TuringMachine) (hM : M.Halts) :
    TokenGame.Refutable (familyR M).toFinset 3 :=
  three_of_board (fun _ hn _ hx => ⟨boardF _, board hn hx⟩) M hM

end FNE.Three
