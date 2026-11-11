/-
# §9.4: the forced word and the contradiction (`thr:quarters`, `thr:roles`, `thr:meet`,
# `thm:three` from (Q5))

* (Q5) as a statement about a word `W = σⁿ(𝔞)` and a finite set `F` of free coordinates
  (`IsBoard`; 07:29–34): (a) `sub`, `cen`, `many`; (b) `seed`; (c) `nowall`, `row`, `col`
  (`RowCorridor`, `ColCorridor`: the nearest light walls in the row and in the column).
  `prop:board` proves it for every word (`Three/Board.lean`).
* `WordSetup`: tokens `1, 2` hold a pin pair whose walker lists are the word (`thr:word`).
* **`thr:quarters`** (`WordSetup.quarters`), the walks along a corridor (`walk_right`, …),
  **`thr:roles`** (`WordSetup.roles_h`, `WordSetup.roles_v`), the palettes of the selected
  component (`Pal`, `pal_of_walker`), **`thr:meet`** (`pal_mv`, `meet_E`, `meet_N`; the meet of the
  finitely many payloads is `payInf`), the compression (`row_chain`, `col_chain`).
* **`thm:three`** from (Q5) (`three_of_board`).

**[choice]** The meet `⋀ U_v` is taken componentwise in the lattice of finite sets (`payInf`;
on nonempty sets it is the iterated `∧` of `prop:horn`(a), `payInf_mem`). (Q5)(a) is used through
an enumeration `f₀ < f₁ < …` of the free coordinates `≥ 2Δ_n + 1` (`Enum`, `exists_enum`). The
channel equalities `(m_v)_E = (m_{v+e₁})_W` are proved for every site `v` (`meet_E`); the paper
states them on channel edges, the only place they are used.
-/
import FixedNoiseErgodicity.Three.Promote
import FixedNoiseErgodicity.Family.HornHalt

set_option autoImplicit false

namespace FNE.Three

open FNE FNE.Scaffold FNE.Family FNE.TokenGame

/-! ## (Q5): the initialized board -/

/-- (Q5): `Δ_n = 4^{n-1}`. -/
def bD (n : ℕ) : ℤ := 4 ^ (n - 1)

/-- (Q5): `z ∈ J = [Δ_n + 1, 3Δ_n]`. -/
def InJ (n : ℕ) (z : ℤ) : Prop := bD n + 1 ≤ z ∧ z ≤ 3 * bD n

/-- (Q5): `z ∈ J° = [Δ_n + 2, 3Δ_n − 1]`. -/
def InJo (n : ℕ) (z : ℤ) : Prop := bD n + 2 ≤ z ∧ z ≤ 3 * bD n - 1

/-- The side of the light vertical wall at the quarter of `W` at `ξ`, if any. -/
def vwq (Wd : Plane → Letter) (ξ : Plane) : Option Family.Side := vWall (quad ξ) (Wd (half ξ))

/-- The side of the light horizontal wall at the quarter of `W` at `ξ`, if any. -/
def hwq (Wd : Plane → Letter) (ξ : Plane) : Option Family.Side := hWall (quad ξ) (Wd (half ξ))

/-- (Q5)(c): `ξ ∈ Z_W = (𝓕 × J°) ∪ (J° × 𝓕)`. -/
def InZW (n : ℕ) (F : Finset ℤ) (ξ : Plane) : Prop :=
  (ξ.1 ∈ F ∧ InJo n ξ.2) ∨ (InJo n ξ.1 ∧ ξ.2 ∈ F)

/-- (Q5)(c), rows: the nearest quarters to the right (`ξ + m e₁`) and to the left (`ξ − m' e₁`)
of `ξ` in its row that lie on a light vertical wall lie in `J × {ξ₂}`, and they are a left side
and a right side, in this order, iff `ξ₂ ∈ 𝓕`. -/
def RowCorridor (n : ℕ) (Wd : Plane → Letter) (F : Finset ℤ) (ξ : Plane) : Prop :=
  ∃ m m' : ℕ, 0 < m ∧ 0 < m' ∧ InJ n (ξ.1 + m) ∧ InJ n (ξ.1 - m') ∧
    vwq Wd (ξ.1 + m, ξ.2) ≠ none ∧ vwq Wd (ξ.1 - m', ξ.2) ≠ none ∧
    (∀ k : ℕ, 0 < k → k < m → vwq Wd (ξ.1 + k, ξ.2) = none) ∧
    (∀ k : ℕ, 0 < k → k < m' → vwq Wd (ξ.1 - k, ξ.2) = none) ∧
    (vwq Wd (ξ.1 - m', ξ.2) = some .lo ∧ vwq Wd (ξ.1 + m, ξ.2) = some .hi ↔ ξ.2 ∈ F)

/-- (Q5)(c), columns: the nearest quarters above and below `ξ` that lie on a light horizontal
wall lie in `{ξ₁} × J`, and they are a bottom side and a top side, in this order, iff
`ξ₁ ∈ 𝓕`. -/
def ColCorridor (n : ℕ) (Wd : Plane → Letter) (F : Finset ℤ) (ξ : Plane) : Prop :=
  ∃ m m' : ℕ, 0 < m ∧ 0 < m' ∧ InJ n (ξ.2 + m) ∧ InJ n (ξ.2 - m') ∧
    hwq Wd (ξ.1, ξ.2 + m) ≠ none ∧ hwq Wd (ξ.1, ξ.2 - m') ≠ none ∧
    (∀ k : ℕ, 0 < k → k < m → hwq Wd (ξ.1, ξ.2 + k) = none) ∧
    (∀ k : ℕ, 0 < k → k < m' → hwq Wd (ξ.1, ξ.2 - k) = none) ∧
    (hwq Wd (ξ.1, ξ.2 - m') = some .lo ∧ hwq Wd (ξ.1, ξ.2 + m) = some .hi ↔ ξ.1 ∈ F)

/-- **(Q5)** for the word `Wd` on `[0, 4ⁿ)²`, with free coordinates `F`. -/
structure IsBoard (n : ℕ) (Wd : Plane → Letter) (F : Finset ℤ) : Prop where
  /-- `𝓕 ⊆ J°` -/
  sub : ∀ z ∈ F, InJo n z
  /-- (a) `2Δ_n + 1 ∈ 𝓕` -/
  cen : 2 * bD n + 1 ∈ F
  /-- (a) at least `2ⁿ − 1` elements of `𝓕` are `≥ 2Δ_n + 1` -/
  many : 2 ^ n - 1 ≤ (F.filter fun z => 2 * bD n + 1 ≤ z).card
  /-- (b) the quarter at `(2Δ_n + 1, 2Δ_n + 1)` is the north-east quarter of the index-`0`
  letter with dark ruler bits -/
  seed : quarter Wd (2 * bD n + 1, 2 * bD n + 1) = ⟨(true, true), index0Dark⟩
  /-- (c) no light wall on `Z_W` -/
  nowall : ∀ ξ, InZW n F ξ → vwq Wd ξ = none ∧ hwq Wd ξ = none
  /-- (c) rows -/
  row : ∀ ξ, InZW n F ξ → RowCorridor n Wd F ξ
  /-- (c) columns -/
  col : ∀ ξ, InZW n F ξ → ColCorridor n Wd F ξ

theorem bD_pos (n : ℕ) : 0 < bD n := by unfold bD; positivity

theorem four_pow_eq_bD {n : ℕ} (hn : 1 ≤ n) : (4 : ℤ) ^ n = 4 * bD n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [bD, Nat.add_sub_cancel, pow_succ]; ring

/-- `J ⊆ [0, 2·4ⁿ)`. -/
theorem inSq_of_J {n : ℕ} (hn : 1 ≤ n) {a b : ℤ} (ha : InJ n a) (hb : InJ n b) :
    InSq (2 * 4 ^ n) (a, b) := by
  have h4 := four_pow_eq_bD hn
  have hp := bD_pos n
  simp only [InSq, InJ] at *
  push_cast
  rw [h4]
  omega

theorem InJo.inJ {n : ℕ} {z : ℤ} (h : InJo n z) : InJ n z := by
  unfold InJo at h; unfold InJ; omega

/-! ## The walker on a forced word -/

variable {M : TuringMachine}

theorem bitZ_inj {a b : Bool} (h : bitZ a = bitZ b) : a = b := by
  cases a <;> cases b <;> simp_all [bitZ]

section Cell

variable {W : Set (State (RM M) 3)} {γ : Plane} {P : PinPair (RM M)}

/-- The class of the walker's centre is `γ`. -/
theorem walker_cls (hγ : ∀ st ∈ W, ∀ i, cls (st.1 i) (ctr (st.2 i)) = γ) {x : Plane}
    {s : LiveSymbol (RM M)} (h : (x, s) ∈ walker W P) : cls x (ctr s) = γ := hγ _ h 2

/-- At the site `ι(z) + ς` of the cell of `z`, the walker's centre has quadrant `ς`. -/
theorem quad_cell (hγ : ∀ st ∈ W, ∀ i, cls (st.1 i) (ctr (st.2 i)) = γ) {z : Plane}
    {b1 b2 : Bool} {s : LiveSymbol (RM M)} (h : (iota γ z + (bitZ b1, bitZ b2), s) ∈ walker W P) :
    tquad (ctr s) = (b1, b2) := by
  obtain ⟨h1, h2⟩ := quad_of_cls (walker_cls hγ h)
  simp only [iota, Prod.fst_add, Prod.snd_add] at h1 h2
  have i1 := bitZ_nonneg b1
  have i2 := bitZ_le_one b1
  have i3 := bitZ_nonneg b2
  have i4 := bitZ_le_one b2
  have e1 : bitZ (tquad (ctr s)).1 = bitZ b1 := by rw [h1]; omega
  have e2 : bitZ (tquad (ctr s)).2 = bitZ b2 := by rw [h2]; omega
  exact Prod.ext (bitZ_inj e1) (bitZ_inj e2)

/-- One step west inside a cell keeps the parent. -/
theorem cell_step1 (hW : IsPlaneSafe W) (hγ : ∀ st ∈ W, ∀ i, cls (st.1 i) (ctr (st.2 i)) = γ)
    {z : Plane} {b1 b2 : Bool} {s : LiveSymbol (RM M)}
    (h : (iota γ z + (bitZ b1, bitZ b2), s) ∈ walker W P) :
    ∃ s', (iota γ z + (bitZ false, bitZ b2), s') ∈ walker W P ∧ tpar (ctr s') = tpar (ctr s) := by
  cases b1
  · exact ⟨s, h, rfl⟩
  · obtain ⟨s', hc, hs'⟩ := walker_move hW h (d := (-1, 0)) (by decide)
    have e : iota γ z + (bitZ true, bitZ b2) + (-1, 0) = iota γ z + (bitZ false, bitZ b2) := by
      ext <;> simp [bitZ]
    rw [e] at hs'
    refine ⟨s', hs', ?_⟩
    have hq := quad_cell hγ hs'
    obtain ⟨-, -, hp⟩ := Q1_E (ctr_mem s') (ctr_mem s) (ctr_match_e1' hc)
    rw [hq] at hp
    simp only [Bool.false_eq_true, false_and, or_false, true_and] at hp
    exact hp.symm

/-- One step south inside a cell keeps the parent. -/
theorem cell_step2 (hW : IsPlaneSafe W) (hγ : ∀ st ∈ W, ∀ i, cls (st.1 i) (ctr (st.2 i)) = γ)
    {z : Plane} {b2 : Bool} {s : LiveSymbol (RM M)}
    (h : (iota γ z + (bitZ false, bitZ b2), s) ∈ walker W P) :
    ∃ s', (iota γ z, s') ∈ walker W P ∧ tpar (ctr s') = tpar (ctr s) := by
  cases b2
  · refine ⟨s, ?_, rfl⟩
    rwa [show iota γ z + (bitZ false, bitZ false) = iota γ z by ext <;> simp [bitZ]] at h
  · obtain ⟨s', hc, hs'⟩ := walker_move hW h (d := (0, -1)) (by decide)
    have e : iota γ z + (bitZ false, bitZ true) + (0, -1) = iota γ z + (bitZ false, bitZ false) := by
      ext <;> simp [bitZ]
    rw [e] at hs'
    have hq := quad_cell hγ hs'
    rw [show iota γ z + (bitZ false, bitZ false) = iota γ z by ext <;> simp [bitZ]] at hs'
    refine ⟨s', hs', ?_⟩
    obtain ⟨-, -, hp⟩ := Q1_N (ctr_mem s') (ctr_mem s) (ctr_match_e2' hc)
    rw [hq] at hp
    simp only [Bool.false_eq_true, false_and, or_false, true_and] at hp
    exact hp.symm

/-- The parent of the walker's centre at a site of the cell of `z` lies in `𝓛_𝐩(z)` (the proof of
`thr:quarters`: moves inside the cell, (Q1)). -/
theorem cell_par (hW : IsPlaneSafe W) (hγ : ∀ st ∈ W, ∀ i, cls (st.1 i) (ctr (st.2 i)) = γ)
    {z : Plane} {b1 b2 : Bool} {s : LiveSymbol (RM M)}
    (h : (iota γ z + (bitZ b1, bitZ b2), s) ∈ walker W P) : tpar (ctr s) ∈ indexLists W γ P z := by
  obtain ⟨s1, h1, e1⟩ := cell_step1 hW hγ h
  obtain ⟨s2, h2, e2⟩ := cell_step2 hW hγ h1
  exact ⟨s2, h2, by rw [e2, e1]⟩

end Cell

/-- The hypotheses of §9.4: tokens `1, 2` hold a pin pair whose walker lists on `y_r + [0,4ⁿ)²`
are the word `Wd` (`thr:word`), and every state of `𝒲` has class `γ`. -/
structure WordSetup (W : Set (State (RM M) 3)) (γ : Plane) (P : PinPair (RM M)) (n : ℕ)
    (yr : Plane) (Wd : Plane → Letter) : Prop where
  safe : IsPlaneSafe W
  hcls : ∀ st ∈ W, ∀ i, cls (st.1 i) (ctr (st.2 i)) = γ
  pin : IsPinPair W P
  word : ∀ y ∈ square 0 (4 ^ n), indexLists W γ P (yr + y) = {Wd y}

namespace WordSetup

variable {W : Set (State (RM M) 3)} {γ : Plane} {P : PinPair (RM M)} {n : ℕ} {yr : Plane}
  {Wd : Plane → Letter} (S : WordSetup W γ P n yr Wd)
include S

/-- **`thr:quarters`.** For `ξ ∈ [0, 2·4ⁿ)²` and `(o + ξ, s) ∈ 𝒳_𝐩`, with `o = ι(y_r)`, the scaffold
pair of `ctr(s)` is the quarter of `W` at `ξ`. -/
theorem quarters {ξ : Plane} (hξ : InSq (2 * 4 ^ n) ξ) {s : LiveSymbol (RM M)}
    (h : (iota γ yr + ξ, s) ∈ walker W P) : spair (ctr s) = quarter Wd ξ := by
  have e : iota γ yr + ξ = iota γ (yr + half ξ) + (bitZ (quad ξ).1, bitZ (quad ξ).2) := by
    obtain ⟨a, b⟩ := ξ
    simp only [quad, half, bitZ_decide_emod_two]
    ext <;> simp [iota] <;> omega
  rw [e] at h
  have hq := quad_cell S.hcls h
  have hp := cell_par S.safe S.hcls h
  have hsq : half ξ ∈ square 0 (4 ^ n) := by
    obtain ⟨a, b⟩ := ξ
    simp only [InSq] at hξ
    push_cast at hξ
    simp only [square, half, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, zero_add]
    push_cast
    generalize (4 : ℤ) ^ n = K at hξ ⊢
    omega
  rw [S.word _ hsq, Set.mem_singleton_iff] at hp
  show (⟨tquad (ctr s), tpar (ctr s)⟩ : SPair) = _
  rw [hq, hp, quarter_apply]

omit S in
/-- The light walls at a tile are those of its scaffold pair. -/
theorem walls_of_spair {t : Tile} {ξ : Plane} (hq : spair t = quarter Wd ξ) :
    vWall (tquad t) (tpar t) = vwq Wd ξ ∧ hWall (tquad t) (tpar t) = hwq Wd ξ := by
  simp [tquad, tpar, hq, quarter_apply, vwq, hwq]

/-- Walking right along a corridor of quarters on no light vertical wall keeps the west flow
(`thr:roles`, proof). -/
theorem walk_right {a b : ℤ} {s : LiveSymbol (RM M)} (h : (iota γ yr + (a, b), s) ∈ walker W P)
    {m : ℕ} (hbox : ∀ k : ℕ, k ≤ m → InSq (2 * 4 ^ n) (a + k, b))
    (hnw : ∀ k : ℕ, k < m → vwq Wd (a + k, b) = none) :
    ∀ l : ℕ, l ≤ m → ∃ s', (iota γ yr + (a + l, b), s') ∈ walker W P ∧
      flowW (ctr s') = flowW (ctr s) := by
  intro l
  induction l with
  | zero => intro _; exact ⟨s, by simpa using h, rfl⟩
  | succ l ih =>
    intro hl
    obtain ⟨s1, hs1, e1⟩ := ih (by omega)
    obtain ⟨s2, hc, hs2⟩ := walker_move S.safe hs1 (d := (1, 0)) (by decide)
    refine ⟨s2, ?_, ?_⟩
    · convert hs2 using 2
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add, Nat.cast_one] <;> ring
    · have hr := Q2_rulesH (ctr_mem s1)
      rw [(walls_of_spair (S.quarters (hbox l (by omega)) hs1)).1, hnw l (by omega)] at hr
      have hr' : flowW (ctr s1) = flowE (ctr s1) := hr
      rw [← Q2_E (ctr_mem s1) (ctr_mem s2) (ctr_match_e1 hc), ← hr', e1]

/-- Walking left keeps the east flow. -/
theorem walk_left {a b : ℤ} {s : LiveSymbol (RM M)} (h : (iota γ yr + (a, b), s) ∈ walker W P)
    {m : ℕ} (hbox : ∀ k : ℕ, k ≤ m → InSq (2 * 4 ^ n) (a - k, b))
    (hnw : ∀ k : ℕ, k < m → vwq Wd (a - k, b) = none) :
    ∀ l : ℕ, l ≤ m → ∃ s', (iota γ yr + (a - l, b), s') ∈ walker W P ∧
      flowE (ctr s') = flowE (ctr s) := by
  intro l
  induction l with
  | zero => intro _; exact ⟨s, by simpa using h, rfl⟩
  | succ l ih =>
    intro hl
    obtain ⟨s1, hs1, e1⟩ := ih (by omega)
    obtain ⟨s2, hc, hs2⟩ := walker_move S.safe hs1 (d := (-1, 0)) (by decide)
    refine ⟨s2, ?_, ?_⟩
    · convert hs2 using 2
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add, Nat.cast_one] <;> ring
    · have hr := Q2_rulesH (ctr_mem s1)
      rw [(walls_of_spair (S.quarters (hbox l (by omega)) hs1)).1, hnw l (by omega)] at hr
      have hr' : flowW (ctr s1) = flowE (ctr s1) := hr
      rw [Q2_E (ctr_mem s2) (ctr_mem s1) (ctr_match_e1' hc), hr', e1]

/-- Walking up along a corridor of quarters on no light horizontal wall keeps the south flow. -/
theorem walk_up {a b : ℤ} {s : LiveSymbol (RM M)} (h : (iota γ yr + (a, b), s) ∈ walker W P)
    {m : ℕ} (hbox : ∀ k : ℕ, k ≤ m → InSq (2 * 4 ^ n) (a, b + k))
    (hnw : ∀ k : ℕ, k < m → hwq Wd (a, b + k) = none) :
    ∀ l : ℕ, l ≤ m → ∃ s', (iota γ yr + (a, b + l), s') ∈ walker W P ∧
      flowS (ctr s') = flowS (ctr s) := by
  intro l
  induction l with
  | zero => intro _; exact ⟨s, by simpa using h, rfl⟩
  | succ l ih =>
    intro hl
    obtain ⟨s1, hs1, e1⟩ := ih (by omega)
    obtain ⟨s2, hc, hs2⟩ := walker_move S.safe hs1 (d := (0, 1)) (by decide)
    refine ⟨s2, ?_, ?_⟩
    · convert hs2 using 2
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add, Nat.cast_one] <;> ring
    · have hr := Q2_rulesV (ctr_mem s1)
      rw [(walls_of_spair (S.quarters (hbox l (by omega)) hs1)).2, hnw l (by omega)] at hr
      have hr' : flowS (ctr s1) = flowN (ctr s1) := hr
      rw [← Q2_N (ctr_mem s1) (ctr_mem s2) (ctr_match_e2 hc), ← hr', e1]

/-- Walking down keeps the north flow. -/
theorem walk_down {a b : ℤ} {s : LiveSymbol (RM M)} (h : (iota γ yr + (a, b), s) ∈ walker W P)
    {m : ℕ} (hbox : ∀ k : ℕ, k ≤ m → InSq (2 * 4 ^ n) (a, b - k))
    (hnw : ∀ k : ℕ, k < m → hwq Wd (a, b - k) = none) :
    ∀ l : ℕ, l ≤ m → ∃ s', (iota γ yr + (a, b - l), s') ∈ walker W P ∧
      flowN (ctr s') = flowN (ctr s) := by
  intro l
  induction l with
  | zero => intro _; exact ⟨s, by simpa using h, rfl⟩
  | succ l ih =>
    intro hl
    obtain ⟨s1, hs1, e1⟩ := ih (by omega)
    obtain ⟨s2, hc, hs2⟩ := walker_move S.safe hs1 (d := (0, -1)) (by decide)
    refine ⟨s2, ?_, ?_⟩
    · convert hs2 using 2
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add, Nat.cast_one] <;> ring
    · have hr := Q2_rulesV (ctr_mem s1)
      rw [(walls_of_spair (S.quarters (hbox l (by omega)) hs1)).2, hnw l (by omega)] at hr
      have hr' : flowS (ctr s1) = flowN (ctr s1) := hr
      rw [Q2_N (ctr_mem s2) (ctr_mem s1) (ctr_match_e2' hc), hr', e1]

end WordSetup

/-- A corridor between two walls: the common flow `ψ` is empty iff the western (southern) wall is
a left (bottom) side and the eastern (northern) one a right (top) side (`prop:routing`(b)). -/
theorem corridor {s1 s2 : Family.Side} {φ1 ψ φ2 : Flow} (h1 : FlowRules (some s1) φ1 ψ)
    (h2 : FlowRules (some s2) ψ φ2) : ψ = Flow.empty ↔ s1 = .lo ∧ s2 = .hi := by
  obtain ⟨b1, b2⟩ := ψ
  cases s1 <;> cases s2 <;> cases b1 <;> cases b2 <;> simp_all [FlowRules, Flow.empty]

namespace WordSetup

variable {W : Set (State (RM M) 3)} {γ : Plane} {P : PinPair (RM M)} {n : ℕ} {yr : Plane}
  {Wd : Plane → Letter} {F : Finset ℤ} (S : WordSetup W γ P n yr Wd)
include S

omit S in
theorem inJ_of_ZW (hB : IsBoard n Wd F) {ξ : Plane} (hξ : InZW n F ξ) : InJ n ξ.1 ∧ InJ n ξ.2 := by
  rcases hξ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(hB.sub _ h1).inJ, h2.inJ⟩
  · exact ⟨h1.inJ, (hB.sub _ h2).inJ⟩

/-- **`thr:roles`**, horizontal: for `ξ ∈ Z_W` and `(o + ξ, s) ∈ 𝒳_𝐩`, `ctr(s)` is a horizontal
carrier iff `ξ₂ ∈ 𝓕`. -/
theorem roles_h (hn : 1 ≤ n) (hB : IsBoard n Wd F) {ξ : Plane} (hξ : InZW n F ξ)
    {s : LiveSymbol (RM M)} (h : (iota γ yr + ξ, s) ∈ walker W P) :
    IsHCarrier (ctr s) ↔ ξ.2 ∈ F := by
  obtain ⟨hJa, hJb⟩ := inJ_of_ZW hB hξ
  have hnw0 := (hB.nowall _ hξ).1
  obtain ⟨m, m', hm, hm', hJ1, hJ2, hw1, hw2, hmid1, hmid2, hside⟩ := hB.row _ hξ
  obtain ⟨a, b⟩ := ξ
  simp only at hJa hJb hJ1 hJ2 hw1 hw2 hmid1 hmid2 hside hnw0 ⊢
  have h' : (iota γ yr + (a, b), s) ∈ walker W P := h
  obtain ⟨sR, hsR, eR⟩ := S.walk_right h' (m := m)
    (fun k hk => inSq_of_J hn (by unfold InJ at hJa hJ1 ⊢; omega) hJb)
    (fun k hk => by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simpa using hnw0
      · exact hmid1 k hk0 hk) m le_rfl
  obtain ⟨sL, hsL, eL⟩ := S.walk_left h' (m := m')
    (fun k hk => inSq_of_J hn (by unfold InJ at hJa hJ2 ⊢; omega) hJb)
    (fun k hk => by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simpa using hnw0
      · exact hmid2 k hk0 hk) m' le_rfl
  have hq0 := S.quarters (inSq_of_J hn hJa hJb) h'
  have e0 : flowW (ctr s) = flowE (ctr s) := by
    have := Q2_rulesH (ctr_mem s)
    rw [(walls_of_spair hq0).1, hnw0] at this
    exact this
  obtain ⟨s2, hs2⟩ := Option.ne_none_iff_exists'.1 hw1
  obtain ⟨s1, hs1⟩ := Option.ne_none_iff_exists'.1 hw2
  have r2 := Q2_rulesH (ctr_mem sR)
  rw [(walls_of_spair (S.quarters (inSq_of_J hn hJ1 hJb) hsR)).1, hs2, eR] at r2
  have r1 := Q2_rulesH (ctr_mem sL)
  rw [(walls_of_spair (S.quarters (inSq_of_J hn hJ2 hJb) hsL)).1, hs1, eL, ← e0] at r1
  have key := corridor r1 r2
  rw [← hside, hs1, hs2, Option.some.injEq, Option.some.injEq, ← key, IsHCarrier, ← e0, and_self]

/-- **`thr:roles`**, vertical: `ctr(s)` is a vertical carrier iff `ξ₁ ∈ 𝓕`. -/
theorem roles_v (hn : 1 ≤ n) (hB : IsBoard n Wd F) {ξ : Plane} (hξ : InZW n F ξ)
    {s : LiveSymbol (RM M)} (h : (iota γ yr + ξ, s) ∈ walker W P) :
    IsVCarrier (ctr s) ↔ ξ.1 ∈ F := by
  obtain ⟨hJa, hJb⟩ := inJ_of_ZW hB hξ
  have hnw0 := (hB.nowall _ hξ).2
  obtain ⟨m, m', hm, hm', hJ1, hJ2, hw1, hw2, hmid1, hmid2, hside⟩ := hB.col _ hξ
  obtain ⟨a, b⟩ := ξ
  simp only at hJa hJb hJ1 hJ2 hw1 hw2 hmid1 hmid2 hside hnw0 ⊢
  have h' : (iota γ yr + (a, b), s) ∈ walker W P := h
  obtain ⟨sU, hsU, eU⟩ := S.walk_up h' (m := m)
    (fun k hk => inSq_of_J hn hJa (by unfold InJ at hJb hJ1 ⊢; omega))
    (fun k hk => by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simpa using hnw0
      · exact hmid1 k hk0 hk) m le_rfl
  obtain ⟨sD, hsD, eD⟩ := S.walk_down h' (m := m')
    (fun k hk => inSq_of_J hn hJa (by unfold InJ at hJb hJ2 ⊢; omega))
    (fun k hk => by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simpa using hnw0
      · exact hmid2 k hk0 hk) m' le_rfl
  have hq0 := S.quarters (inSq_of_J hn hJa hJb) h'
  have e0 : flowS (ctr s) = flowN (ctr s) := by
    have := Q2_rulesV (ctr_mem s)
    rw [(walls_of_spair hq0).2, hnw0] at this
    exact this
  obtain ⟨s2, hs2⟩ := Option.ne_none_iff_exists'.1 hw1
  obtain ⟨s1, hs1⟩ := Option.ne_none_iff_exists'.1 hw2
  have r2 := Q2_rulesV (ctr_mem sU)
  rw [(walls_of_spair (S.quarters (inSq_of_J hn hJa hJ1) hsU)).2, hs2, eU] at r2
  have r1 := Q2_rulesV (ctr_mem sD)
  rw [(walls_of_spair (S.quarters (inSq_of_J hn hJa hJ2) hsD)).2, hs1, eD, ← e0] at r1
  have key := corridor r1 r2
  rw [← hside, hs1, hs2, Option.some.injEq, Option.some.injEq, ← key, IsVCarrier, ← e0, and_self]

end WordSetup

/-! ## Meets of payloads -/

/-- The componentwise meet of a finite set of payloads (`∅` colours for the empty set). -/
noncomputable def payInf (U : Finset Pay) : Pay :=
  if h : U.Nonempty then ⟨U.inf' h Pay.W, U.inf' h Pay.E, U.inf' h Pay.S, U.inf' h Pay.N⟩
  else ⟨∅, ∅, ∅, ∅⟩

theorem payInf_of_nonempty {U : Finset Pay} (h : U.Nonempty) :
    payInf U = ⟨U.inf' h Pay.W, U.inf' h Pay.E, U.inf' h Pay.S, U.inf' h Pay.N⟩ := dif_pos h

/-- On nonempty sets `payInf` is the iterated `∧` of `prop:horn`(a): a predicate closed under `∧`
and true on every element holds for the meet. -/
theorem payInf_mem {Q : Pay → Prop} (hQ : ∀ c c', Q c → Q c' → Q (c.meet c'))
    {U : Finset Pay} (hne : U.Nonempty) (hU : ∀ c ∈ U, Q c) : Q (payInf U) := by
  induction hne using Finset.Nonempty.cons_induction with
  | singleton a =>
    rw [payInf_of_nonempty (Finset.singleton_nonempty a)]
    simpa using hU a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    rw [payInf_of_nonempty (Finset.cons_nonempty ha)]
    have h1 := hU a (Finset.mem_cons_self a s)
    have h2 := ih (fun c hc => hU c (Finset.mem_cons_of_mem hc))
    rw [payInf_of_nonempty hs] at h2
    have := hQ _ _ h1 h2
    convert this using 1
    ext1 <;> simp only [Pay.meet, Finset.inf'_cons hs, Finset.inf_eq_inter]

/-- `thr:meet`(b), the core: if every element of `U` has an element of `V` with `c_E = d_W` and
conversely, the meets satisfy `(⋀U)_E = (⋀V)_W`. -/
theorem payInf_EW {U V : Finset Pay} (hU : U.Nonempty) (hV : V.Nonempty)
    (h1 : ∀ c ∈ U, ∃ d ∈ V, c.E = d.W) (h2 : ∀ d ∈ V, ∃ c ∈ U, c.E = d.W) :
    (payInf U).E = (payInf V).W := by
  rw [payInf_of_nonempty hU, payInf_of_nonempty hV]
  apply le_antisymm
  · refine Finset.le_inf' hV _ fun d hd => ?_
    obtain ⟨c, hc, e⟩ := h2 d hd
    exact e ▸ Finset.inf'_le Pay.E hc
  · refine Finset.le_inf' hU _ fun c hc => ?_
    obtain ⟨d, hd, e⟩ := h1 c hc
    exact e ▸ Finset.inf'_le Pay.W hd

theorem payInf_NS {U V : Finset Pay} (hU : U.Nonempty) (hV : V.Nonempty)
    (h1 : ∀ c ∈ U, ∃ d ∈ V, c.N = d.S) (h2 : ∀ d ∈ V, ∃ c ∈ U, c.N = d.S) :
    (payInf U).N = (payInf V).S := by
  rw [payInf_of_nonempty hU, payInf_of_nonempty hV]
  apply le_antisymm
  · refine Finset.le_inf' hV _ fun d hd => ?_
    obtain ⟨c, hc, e⟩ := h2 d hd
    exact e ▸ Finset.inf'_le Pay.N hc
  · refine Finset.le_inf' hU _ fun c hc => ?_
    obtain ⟨d, hd, e⟩ := h1 c hc
    exact e ▸ Finset.inf'_le Pay.S hd

section Meet

variable {W : Set (State (RM M) 3)} {P : PinPair (RM M)}

open Classical in
/-- `thr:meet`: `U_v = {pay(ctr(s)) : (v, s) ∈ 𝒳_𝐩}`, a finite set (the centres are tiles of
`R_M`). -/
noncomputable def Uset (W : Set (State (RM M) 3)) (P : PinPair (RM M)) (v : Plane) : Finset Pay :=
  ((RM M).filter fun t => ∃ s, (v, s) ∈ walker W P ∧ ctr s = t).image tpay

theorem mem_Uset {v : Plane} {c : Pay} :
    c ∈ Uset W P v ↔ ∃ s, (v, s) ∈ walker W P ∧ tpay (ctr s) = c := by
  classical
  simp only [Uset, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨t, ⟨-, s, hs, rfl⟩, rfl⟩; exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩; exact ⟨ctr s, ⟨ctr_mem s, s, hs, rfl⟩, rfl⟩

theorem Uset_nonempty (hW : IsPlaneSafe W) (hP : IsPinPair W P) (v : Plane) :
    (Uset W P v).Nonempty := by
  obtain ⟨s, hs⟩ := walker_total hW hP v
  exact ⟨_, mem_Uset.2 ⟨s, hs, rfl⟩⟩

/-- `thr:meet`: `m_v = ⋀ U_v`. -/
noncomputable def mv (W : Set (State (RM M) 3)) (P : PinPair (RM M)) (v : Plane) : Pay :=
  payInf (Uset W P v)

/-- **`thr:meet`(b)**, horizontally: `(m_v)_E = (m_{v + e₁})_W` (for every site `v`). -/
theorem meet_E (hW : IsPlaneSafe W) (hP : IsPinPair W P) (v : Plane) :
    (mv W P v).E = (mv W P (v + (1, 0))).W := by
  refine payInf_EW (Uset_nonempty hW hP v) (Uset_nonempty hW hP _) ?_ ?_
  · intro c hc
    obtain ⟨s, hs, rfl⟩ := mem_Uset.1 hc
    obtain ⟨s', hc', hs'⟩ := walker_move hW hs (d := (1, 0)) (by decide)
    exact ⟨_, mem_Uset.2 ⟨s', hs', rfl⟩, Q3_E (ctr_mem s) (ctr_mem s') (ctr_match_e1 hc')⟩
  · intro d hd
    obtain ⟨s', hs', rfl⟩ := mem_Uset.1 hd
    obtain ⟨s, hc, hs⟩ := walker_move hW hs' (d := (-1, 0)) (by decide)
    rw [show v + (1, 0) + (-1, 0) = v by ext <;> simp] at hs
    exact ⟨_, mem_Uset.2 ⟨s, hs, rfl⟩, Q3_E (ctr_mem s) (ctr_mem s') (ctr_match_e1' hc)⟩

/-- **`thr:meet`(b)**, vertically: `(m_v)_N = (m_{v + e₂})_S`. -/
theorem meet_N (hW : IsPlaneSafe W) (hP : IsPinPair W P) (v : Plane) :
    (mv W P v).N = (mv W P (v + (0, 1))).S := by
  refine payInf_NS (Uset_nonempty hW hP v) (Uset_nonempty hW hP _) ?_ ?_
  · intro c hc
    obtain ⟨s, hs, rfl⟩ := mem_Uset.1 hc
    obtain ⟨s', hc', hs'⟩ := walker_move hW hs (d := (0, 1)) (by decide)
    exact ⟨_, mem_Uset.2 ⟨s', hs', rfl⟩, Q3_N (ctr_mem s) (ctr_mem s') (ctr_match_e2 hc')⟩
  · intro d hd
    obtain ⟨s', hs', rfl⟩ := mem_Uset.1 hd
    obtain ⟨s, hc, hs⟩ := walker_move hW hs' (d := (0, -1)) (by decide)
    rw [show v + (0, 1) + (0, -1) = v by ext <;> simp] at hs
    exact ⟨_, mem_Uset.2 ⟨s, hs, rfl⟩, Q3_N (ctr_mem s) (ctr_mem s') (ctr_match_e2' hc)⟩

end Meet

/-! ## The selected component (07:117–130) -/

/-- An enumeration `f₀ < f₁ < … < f_{N−1}` of the `N` smallest free coordinates `≥ c₀`, with
`f₀ = c₀`; every free coordinate between `f₀` and `f_{N−1}` is one of them. -/
structure Enum (F : Finset ℤ) (c0 : ℤ) (N : ℕ) (f : ℕ → ℤ) : Prop where
  zero : f 0 = c0
  mem : ∀ i < N, f i ∈ F
  mono : ∀ i j, i < j → j < N → f i < f j
  cover : ∀ z ∈ F, f 0 ≤ z → z ≤ f (N - 1) → ∃ i < N, f i = z

theorem exists_enum (F : Finset ℤ) (c0 : ℤ) (hc : c0 ∈ F) (N : ℕ) (hN : 1 ≤ N)
    (hcard : N ≤ (F.filter fun z => c0 ≤ z).card) : ∃ f, Enum F c0 N f := by
  set S := F.filter fun z => c0 ≤ z with hS
  have hcS : c0 ∈ S := Finset.mem_filter.2 ⟨hc, le_rfl⟩
  let e := S.orderEmbOfFin rfl
  refine ⟨fun i => if h : i < S.card then e ⟨i, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · have h0 : 0 < S.card := by omega
    simp only [dif_pos h0]
    rw [Finset.orderEmbOfFin_zero rfl h0]
    refine le_antisymm (Finset.min'_le _ _ hcS) (Finset.le_min' _ _ _ fun y hy => ?_)
    exact (Finset.mem_filter.1 hy).2
  · intro i hi
    simp only [dif_pos (show i < S.card by omega)]
    exact (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem S rfl _)).1
  · intro i j hij hj
    simp only [dif_pos (show i < S.card by omega), dif_pos (show j < S.card by omega)]
    exact e.strictMono (Fin.mk_lt_mk.2 hij)
  · intro z hz h0 h1
    have h0' : 0 < S.card := by omega
    have hN' : N - 1 < S.card := by omega
    simp only [dif_pos h0', dif_pos hN'] at h0 h1
    have hzS : z ∈ S := by
      refine Finset.mem_filter.2 ⟨hz, ?_⟩
      rw [Finset.orderEmbOfFin_zero rfl h0'] at h0
      exact le_trans (Finset.le_min' _ _ _ fun y hy => (Finset.mem_filter.1 hy).2) h0
    have : z ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hzS
    obtain ⟨k, rfl⟩ := this
    have hk : k ≤ ⟨N - 1, hN'⟩ := e.le_iff_le.1 h1
    refine ⟨k.1, by have := Fin.le_def.1 hk; simp at this; omega, ?_⟩
    simp only [dif_pos k.2]

section Select

variable {f : ℕ → ℤ} {N : ℕ}

/-- `z ∈ F_N = {f₀, …, f_{N−1}}`. -/
def InFN (f : ℕ → ℤ) (N : ℕ) (z : ℤ) : Prop := ∃ i < N, f i = z

/-- `ξ ∈ Z` (07:119). -/
def InZ (f : ℕ → ℤ) (N : ℕ) (ξ : Plane) : Prop :=
  (InFN f N ξ.2 ∧ f 0 ≤ ξ.1 ∧ ξ.1 ≤ f (N - 1)) ∨ (InFN f N ξ.1 ∧ f 0 ≤ ξ.2 ∧ ξ.2 ≤ f (N - 1))

open Classical in
/-- The palettes `Pal(ξ)` (07:121–129). -/
def Pal (M : TuringMachine) (f : ℕ → ℤ) (N : ℕ) (ξ : Plane) (c : Pay) : Prop :=
  if ξ = (f 0, f 0) then c = seedTile M
  else if InFN f N ξ.1 ∧ InFN f N ξ.2 then InT M c
  else if InFN f N ξ.2 then palette M .horiz c
  else palette M .vert c

/-- Every palette is closed under `∧` (`ref:meet`(a), `prop:horn`(a)). -/
theorem Pal_meet {ξ : Plane} {c c' : Pay} (h : Pal M f N ξ c) (h' : Pal M f N ξ c') :
    Pal M f N ξ (c.meet c') := by
  unfold Pal at h h' ⊢
  split_ifs at h h' ⊢
  · rw [h, h']; exact (palettes_meet (M := M) c c').2.2.2
  · exact h.meet h'
  · exact ⟨(palettes_meet (M := M) c c').1 h.1 h'.1, (palettes_meet (M := M) c c').2.1 h.2 h'.2⟩
  · exact ⟨(palettes_meet (M := M) c c').1 h.1 h'.1,
      (palettes_meet (M := M) c c').2.2.1 h.2 h'.2⟩

theorem Enum.le {F : Finset ℤ} {c0 : ℤ} (hf : Enum F c0 N f) {i j : ℕ} (hij : i ≤ j)
    (hj : j < N) : f i ≤ f j := by
  rcases eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  · exact (hf.mono i j h hj).le

/-- On `Z`, membership in `𝓕` and in `F_N` agree (for both coordinates). -/
theorem Enum.mem_iff {F : Finset ℤ} {c0 : ℤ} (hf : Enum F c0 N f) {z : ℤ} (h0 : f 0 ≤ z)
    (h1 : z ≤ f (N - 1)) : z ∈ F ↔ InFN f N z := by
  constructor
  · intro hz; exact hf.cover z hz h0 h1
  · rintro ⟨i, hi, rfl⟩; exact hf.mem i hi

theorem Enum.bounds {F : Finset ℤ} {c0 : ℤ} (hf : Enum F c0 N f) {z : ℤ} (hz : InFN f N z) :
    f 0 ≤ z ∧ z ≤ f (N - 1) := by
  obtain ⟨i, hi, rfl⟩ := hz
  exact ⟨hf.le (Nat.zero_le i) hi, hf.le (by omega) (by omega)⟩

/-- An integer strictly between `f_i` and `f_{i+1}` is not in `F_N`. -/
theorem Enum.not_mem_between {F : Finset ℤ} {c0 : ℤ} (hf : Enum F c0 N f) {i : ℕ}
    (hi : i + 1 < N) {y : ℤ} (h1 : f i < y) (h2 : y < f (i + 1)) : ¬ InFN f N y := by
  rintro ⟨j, hj, rfl⟩
  rcases lt_trichotomy j i with h | rfl | h
  · exact absurd (hf.le h.le (by omega)) (not_le.2 h1)
  · exact lt_irrefl _ h1
  · exact absurd (hf.le (show i + 1 ≤ j by omega) hj) (not_le.2 h2)

end Select

namespace WordSetup

variable {W : Set (State (RM M) 3)} {γ : Plane} {P : PinPair (RM M)} {n : ℕ} {yr : Plane}
  {Wd : Plane → Letter} {F : Finset ℤ} {f : ℕ → ℤ} {N : ℕ} (S : WordSetup W γ P n yr Wd)
include S

/-- By `thr:roles` and (Q3), the payload of every walker symbol on `o + Z` lies in the palette
(07:130, 09:312). -/
theorem pal_of_walker (hn : 1 ≤ n) (hB : IsBoard n Wd F) (hf : Enum F (2 * bD n + 1) N f)
    (hN : 1 ≤ N) {ξ : Plane} (hξ : InZ f N ξ) {s : LiveSymbol (RM M)}
    (h : (iota γ yr + ξ, s) ∈ walker W P) : Pal M f N ξ (tpay (ctr s)) := by
  -- `Z ⊆ Z_W`, and on `Z` membership in `𝓕` is membership in `F_N`
  have hJo0 : InJo n (f 0) := hB.sub _ (hf.mem 0 hN)
  have hJo1 : InJo n (f (N - 1)) := hB.sub _ (hf.mem (N - 1) (by omega))
  obtain ⟨hb1, hb2⟩ : (f 0 ≤ ξ.1 ∧ ξ.1 ≤ f (N - 1)) ∧ (f 0 ≤ ξ.2 ∧ ξ.2 ≤ f (N - 1)) := by
    rcases hξ with ⟨h2, h1⟩ | ⟨h1, h2⟩
    · exact ⟨h1, hf.bounds h2⟩
    · exact ⟨hf.bounds h1, h2⟩
  have hZW : InZW n F ξ := by
    unfold InJo at hJo0 hJo1
    rcases hξ with ⟨h2, -⟩ | ⟨h1, -⟩
    · exact Or.inr ⟨by unfold InJo; omega, (hf.mem_iff hb2.1 hb2.2).2 h2⟩
    · exact Or.inl ⟨(hf.mem_iff hb1.1 hb1.2).2 h1, by unfold InJo; omega⟩
  have hH := S.roles_h hn hB hZW h
  have hV := S.roles_v hn hB hZW h
  rw [hf.mem_iff hb2.1 hb2.2] at hH
  rw [hf.mem_iff hb1.1 hb1.2] at hV
  have hpal := Q3_palette (ctr_mem s)
  rw [trole_eq] at hpal
  unfold Pal
  split_ifs with h0 h12 h2
  · -- the seed site
    have hq := S.quarters (by
      obtain ⟨hJ1, hJ2⟩ := inJ_of_ZW hB hZW
      exact inSq_of_J hn hJ1 hJ2) h
    rw [h0, hf.zero, hB.seed] at hq
    have hc : IsHCarrier (ctr s) ∧ IsVCarrier (ctr s) := by
      rw [h0] at hH hV
      exact ⟨hH.2 ⟨0, hN, rfl⟩, hV.2 ⟨0, hN, rfl⟩⟩
    rw [if_pos hc, if_pos hq] at hpal
    exact hpal
  · have hc : IsHCarrier (ctr s) ∧ IsVCarrier (ctr s) := ⟨hH.2 h12.2, hV.2 h12.1⟩
    rw [if_pos hc] at hpal
    split_ifs at hpal
    · rw [show tpay (ctr s) = seedTile M from hpal]; exact seedTile_inT M
    · exact hpal
  · have h1 : ¬ InFN f N ξ.1 := fun h1 => h12 ⟨h1, h2⟩
    rw [if_neg (fun hc => h1 (hV.1 hc.2)), if_pos (hH.2 h2)] at hpal
    exact hpal
  · have h1 : InFN f N ξ.1 := by
      rcases hξ with ⟨h2', -⟩ | ⟨h1, -⟩
      · exact absurd h2' h2
      · exact h1
    rw [if_neg (fun hc => h2 (hH.1 hc.1)), if_neg (fun hc => h2 (hH.1 hc)), if_pos (hV.2 h1)]
      at hpal
    exact hpal

/-- **`thr:meet`(a)**: `m_v ∈ Pal(ξ)` for `ξ ∈ Z` and `v = o + ξ`. -/
theorem pal_mv (hn : 1 ≤ n) (hB : IsBoard n Wd F) (hf : Enum F (2 * bD n + 1) N f)
    (hN : 1 ≤ N) {ξ : Plane} (hξ : InZ f N ξ) : Pal M f N ξ (mv W P (iota γ yr + ξ)) :=
  payInf_mem (fun _ _ => Pal_meet) (Uset_nonempty S.safe S.pin _) fun c hc => by
    obtain ⟨s, hs, rfl⟩ := mem_Uset.1 hc
    exact S.pal_of_walker hn hB hf hN hξ hs

/-- The compression along a row (07:170): `(m_{o+(f_i, r)})_E = (m_{o+(f_{i+1}, r)})_W` for `r ∈ F_N`,
through the horizontal palettes strictly between. -/
theorem row_chain (hn : 1 ≤ n) (hB : IsBoard n Wd F) (hf : Enum F (2 * bD n + 1) N f)
    {i : ℕ} (hi : i + 1 < N) {r : ℤ} (hr : InFN f N r) :
    (mv W P (iota γ yr + (f i, r))).E = (mv W P (iota γ yr + (f (i + 1), r))).W := by
  have hlt := hf.mono i (i + 1) (by omega) hi
  have key : ∀ y, f i + 1 ≤ y → y ≤ f (i + 1) →
      (mv W P (iota γ yr + (f i, r))).E = (mv W P (iota γ yr + (y, r))).W := by
    intro y hy
    induction y, hy using Int.leInduction with
    | base =>
      intro _
      rw [meet_E S.safe S.pin]
      congr 2; ext <;> simp [add_assoc]
    | succ y hy ih =>
      intro hy2
      rw [ih (by omega)]
      have hZ : InZ f N (y, r) := Or.inl ⟨hr, by have := hf.le (Nat.zero_le i) (by omega); simp; omega,
        by have := hf.le (show i + 1 ≤ N - 1 by omega) (by omega); simp; omega⟩
      have hp := S.pal_mv hn hB hf (by omega) hZ
      unfold Pal at hp
      have hne : ((y, r) : Plane) ≠ (f 0, f 0) := by
        intro e
        have := hf.le (Nat.zero_le i) (by omega)
        simp only [Prod.mk.injEq] at e; omega
      have hy1 : ¬ InFN f N y := hf.not_mem_between hi (by omega) (by omega)
      rw [if_neg hne, if_neg (fun h => hy1 h.1), if_pos hr] at hp
      rw [hp.2, meet_E S.safe S.pin]
      congr 2; ext <;> simp [add_assoc]
  exact key _ (by omega) le_rfl

/-- The compression along a column: `(m_{o+(c, f_i)})_N = (m_{o+(c, f_{i+1})})_S` for `c ∈ F_N`. -/
theorem col_chain (hn : 1 ≤ n) (hB : IsBoard n Wd F) (hf : Enum F (2 * bD n + 1) N f)
    {i : ℕ} (hi : i + 1 < N) {c : ℤ} (hc : InFN f N c) :
    (mv W P (iota γ yr + (c, f i))).N = (mv W P (iota γ yr + (c, f (i + 1)))).S := by
  have hlt := hf.mono i (i + 1) (by omega) hi
  have key : ∀ y, f i + 1 ≤ y → y ≤ f (i + 1) →
      (mv W P (iota γ yr + (c, f i))).N = (mv W P (iota γ yr + (c, y))).S := by
    intro y hy
    induction y, hy using Int.leInduction with
    | base =>
      intro _
      rw [meet_N S.safe S.pin]
      congr 2; ext <;> simp [add_assoc]
    | succ y hy ih =>
      intro hy2
      rw [ih (by omega)]
      have hZ : InZ f N (c, y) := Or.inr ⟨hc, by have := hf.le (Nat.zero_le i) (by omega); simp; omega,
        by have := hf.le (show i + 1 ≤ N - 1 by omega) (by omega); simp; omega⟩
      have hp := S.pal_mv hn hB hf (by omega) hZ
      unfold Pal at hp
      have hne : ((c, y) : Plane) ≠ (f 0, f 0) := by
        intro e
        have := hf.le (Nat.zero_le i) (by omega)
        simp only [Prod.mk.injEq] at e; omega
      have hy1 : ¬ InFN f N y := hf.not_mem_between hi (by omega) (by omega)
      rw [if_neg hne, if_neg (fun h => hy1 h.2), if_neg hy1] at hp
      rw [hp.2, meet_N S.safe S.pin]
      congr 2; ext <;> simp [add_assoc]
  exact key _ (by omega) le_rfl

end WordSetup

/-! ## `thm:three` from (Q5) -/

/-- **`thm:three`, from (Q5).** If every word `σⁿ(𝔞)`, `n ≥ 2`, carries an initialized board in
the sense of (Q5), then for every machine `M` that halts, `R_M` is `3`-token refutable. -/
theorem three_of_board
    (hB : ∀ n : ℕ, 2 ≤ n → ∀ a : Letter, a.InA → ∃ F, IsBoard n (sigmaPow n a) F)
    (M : TuringMachine) (hM : M.Halts) : Refutable (RM M) 3 := by
  classical
  -- the halting time `T` of `M°`
  have hex := (oHalts_iff M).2 hM
  obtain ⟨T, hT, hmin⟩ : ∃ T, oHalt M (oRun M T).state = true ∧
      ∀ s < T, oHalt M (oRun M s).state = false :=
    ⟨Nat.find hex, Nat.find_spec hex, fun s hs => by simpa using Nat.find_min hex hs⟩
  rw [refutable_iff_not_exists_planeSafe]
  rintro ⟨W0, hne0, hW0⟩
  obtain ⟨γ, hneγ⟩ := exists_classPart hW0 hne0 0
  have hW := classPart_safe hW0 γ
  have hγ : ∀ st ∈ classPart W0 γ, ∀ i, cls (st.1 i) (ctr (st.2 i)) = γ := fun st h => h.2
  -- the depth `n` and the word
  set N := 2 * T + 10 with hNdef
  set n := 2 * T + 12 with hndef
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  obtain ⟨P, hP⟩ := exists_cornerPair hW hγ hneγ (2 * n) (by omega)
  obtain ⟨yr, κr, -, hword⟩ := thr_word hW hγ hn1 hP
  obtain ⟨F, hF⟩ := hB n hn2 (cornerLetter κr true) (cornerLetter_inA κr true)
  have S : WordSetup (classPart W0 γ) γ P n yr (sigmaPow n (cornerLetter κr true)) :=
    ⟨hW, hγ, hP.1, hword⟩
  have hNn : N ≤ 2 ^ n - 1 := by
    have := n.lt_two_pow_self
    omega
  obtain ⟨f, hf⟩ := exists_enum F (2 * bD n + 1) hF.cen N (by omega) (le_trans hNn hF.many)
  -- the compressed pattern
  let Ξ : Plane → Pay := fun u => mv (classPart W0 γ) P (iota γ yr + (f u.1.toNat, f u.2.toNat))
  have hFN : ∀ i : ℤ, 0 ≤ i → i < N → InFN f N (f i.toNat) := fun i h0 h1 => ⟨i.toNat, by omega, rfl⟩
  have hZ : ∀ u, InSq N u → InZ f N (f u.1.toNat, f u.2.toNat) := by
    intro u hu
    obtain ⟨h1, h2, h3, h4⟩ := hu
    exact Or.inl ⟨hFN _ h3 h4, (hf.bounds (hFN _ h1 h2)).1, (hf.bounds (hFN _ h1 h2)).2⟩
  refine horn_c M T hT hmin N (by omega) Ξ ?_ ?_ ?_ ?_
  · intro u hu
    have hp := S.pal_mv hn1 hF hf (by omega) (hZ u hu)
    obtain ⟨h1, h2, h3, h4⟩ := hu
    unfold Pal at hp
    split_ifs at hp with h0 h12
    · show InT M (Ξ u); rw [show Ξ u = seedTile M from hp]; exact seedTile_inT M
    · exact hp
    · exact absurd (⟨hFN _ h1 h2, hFN _ h3 h4⟩ : InFN f N _ ∧ InFN f N _) h12
    · exact absurd (⟨hFN _ h1 h2, hFN _ h3 h4⟩ : InFN f N _ ∧ InFN f N _) h12
  · intro u hu hu'
    obtain ⟨h1, h2, h3, h4⟩ := hu
    have h2' : u.1 + 1 < N := by have := hu'.2.1; simpa using this
    have e : u + (1, 0) = (u.1 + 1, u.2) := by ext <;> simp
    have e' : (u.1 + 1).toNat = u.1.toNat + 1 := by omega
    rw [e]
    show (mv _ P (iota γ yr + (f u.1.toNat, f u.2.toNat))).E =
      (mv _ P (iota γ yr + (f (u.1 + 1).toNat, f u.2.toNat))).W
    rw [e']
    exact S.row_chain hn1 hF hf (by omega) (hFN _ h3 h4)
  · intro u hu hu'
    obtain ⟨h1, h2, h3, h4⟩ := hu
    have h4' : u.2 + 1 < N := by have := hu'.2.2.2; simpa using this
    have e : u + (0, 1) = (u.1, u.2 + 1) := by ext <;> simp
    have e' : (u.2 + 1).toNat = u.2.toNat + 1 := by omega
    rw [e]
    show (mv _ P (iota γ yr + (f u.1.toNat, f u.2.toNat))).N =
      (mv _ P (iota γ yr + (f u.1.toNat, f (u.2 + 1).toNat))).S
    rw [e']
    exact S.col_chain hn1 hF hf (by omega) (hFN _ h1 h2)
  · have hp := S.pal_mv hn1 hF hf (by omega) (hZ (0, 0) ⟨le_rfl, by omega, le_rfl, by omega⟩)
    unfold Pal at hp
    rw [if_pos (by simp)] at hp
    exact hp

end FNE.Three
