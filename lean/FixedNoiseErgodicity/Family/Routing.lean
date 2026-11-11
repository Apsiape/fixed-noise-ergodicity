/-
# Section 6.2 (flows and roles) and 6.4: the routed scaffold and routing on the plane

* `fam:def-routed`: flows, the routed scaffold `𝔸^r` (`RTile`, `RTile.InR`), its matching;
  carriers and roles (06:160).
  **[choice]** A flow `φ ⊆ {left, right}` (or `⊆ {down, up}`) is a pair of Booleans
  `(left ∈ φ, right ∈ φ)` (`Flow`).
* `prop:routing`, stated along one row (a map `T : ℤ → RTile` whose consecutive tiles match):
  `routing`, and "no tile on a light vertical wall is a horizontal carrier".
* A routing on a line: for a set of walls unbounded in both directions, the flows of
  `fam:positive`(a) (nearest wall to the west and to the east of each edge) satisfy the flow rules
  (`lineFlow_rules`).
* `fam:positive`(a) (`positive_a`): the quartering of the bottom tiling of a tower of phase
  `(1/3, 1/3)`, with these flows, is a tiling of `𝔸^r`.
-/
import FixedNoiseErgodicity.Family.Frames

set_option autoImplicit false

namespace FNE.Family

open FNE.Scaffold

/-! ## Flows, the routed scaffold, roles (`fam:def-routed`, 06:160) -/

/-- `fam:def-routed`: a flow `φ ⊆ {left, right}` (or `{down, up}`) as `(left ∈ φ, right ∈ φ)`. -/
abbrev Flow := Bool × Bool

/-- The empty flow. -/
def Flow.empty : Flow := (false, false)

/-- The flow rules on one axis, for the wall side `w` at the tile: (F1) no wall: equal flows;
(F2) a left (bottom) side: the west (south) flow is nonempty and the east (north) flow is
`⊆ {left}` (`⊆ {down}`); (F3) a right (top) side: the east (north) flow is nonempty and the west
(south) flow is `⊆ {right}` (`⊆ {up}`). -/
def FlowRules : Option Side → Flow → Flow → Prop
  | none, φ, φ' => φ = φ'
  | some .lo, φ, φ' => (φ.1 = true ∨ φ.2 = true) ∧ φ'.2 = false
  | some .hi, φ, φ' => (φ'.1 = true ∨ φ'.2 = true) ∧ φ.1 = false

/-- `fam:def-routed`: a tile `(ς, 𝔞, φ_W, φ_E, φ_S, φ_N)` of the routed scaffold. -/
structure RTile where
  /-- the scaffold pair `(ς, 𝔞)` -/
  q : SPair
  /-- west flow -/
  fW : Flow
  /-- east flow -/
  fE : Flow
  /-- south flow -/
  fS : Flow
  /-- north flow -/
  fN : Flow
  deriving DecidableEq

namespace RTile

/-- The side of the light vertical wall at the tile, if any. -/
def vw (t : RTile) : Option Side := vWall t.q.quad t.q.par

/-- The side of the light horizontal wall at the tile, if any. -/
def hw (t : RTile) : Option Side := hWall t.q.quad t.q.par

/-- `fam:def-routed`: the tile lies in `𝔸^r`: its scaffold pair is in `𝔸^q` and the flow rules
(F1)–(F3) hold for `φ_W, φ_E` and (F4)–(F6) for `φ_S, φ_N`. -/
def InR (t : RTile) : Prop := t.q.InQ ∧ FlowRules t.vw t.fW t.fE ∧ FlowRules t.hw t.fS t.fN

/-- `fam:def-routed`: the colour on a side is the pair of the `𝔸^q` colour and the flow; tiles
match horizontally iff the scaffold pairs match and `φ_E = φ'_W`. -/
def MatchE (t t' : RTile) : Prop := t.q.MatchE t'.q ∧ t.fE = t'.fW

/-- Tiles match vertically iff the scaffold pairs match and `φ_N = φ'_S`. -/
def MatchN (t t' : RTile) : Prop := t.q.MatchN t'.q ∧ t.fN = t'.fS

/-- 06:160: a *horizontal carrier* has `φ_W = φ_E = ∅`. -/
def HCarrier (t : RTile) : Prop := t.fW = Flow.empty ∧ t.fE = Flow.empty

/-- 06:160: a *vertical carrier* has `φ_S = φ_N = ∅`. -/
def VCarrier (t : RTile) : Prop := t.fS = Flow.empty ∧ t.fN = Flow.empty

end RTile

/-- The index-`0` letter with dark ruler bits, `(a, ∠b, A, 0, 0)` (06:7). -/
def index0Dark : Letter := ⟨⟨.a, .corner .b, .A⟩, false, false⟩

/-- 06:160: the roles. -/
inductive Role where
  | inactive
  | horiz
  | vert
  | active
  | seed
  deriving DecidableEq

instance (t : RTile) : Decidable t.HCarrier := inferInstanceAs (Decidable (_ ∧ _))

instance (t : RTile) : Decidable t.VCarrier := inferInstanceAs (Decidable (_ ∧ _))

/-- 06:160: the role of a tile: inactive (no carrier), horizontal (only a horizontal carrier),
vertical (only a vertical carrier), active (both), except that an active tile with scaffold pair
`((1,1), 𝔞)`, `𝔞` an index-`0` letter with dark ruler bits, has the seed role. (Computable:
carriers are decidable.) -/
def RTile.role (t : RTile) : Role :=
  if t.HCarrier ∧ t.VCarrier then
    (if t.q = ⟨(true, true), index0Dark⟩ then .seed else .active)
  else if t.HCarrier then .horiz else if t.VCarrier then .vert else .inactive

/-! ## `prop:routing` -/

/-- `prop:routing`(c), second claim: no tile on a light wall (with the flow rules) is a carrier
across that wall. -/
theorem not_carrier_of_wall {s : Side} {φ φ' : Flow} (h : FlowRules (some s) φ φ') :
    ¬ (φ = Flow.empty ∧ φ' = Flow.empty) := by
  rintro ⟨rfl, rfl⟩
  cases s <;> simp [FlowRules, Flow.empty] at h

/-- **`prop:routing`**, along a row `T : ℤ → RTile` whose tiles at `w₁ ≤ x ≤ w₂` obey the flow
rules and match on consecutive edges. Suppose `T w₁` and `T w₂` lie on light vertical walls with
sides `s₁, s₂` and the tiles strictly between do not. Then (a) the flows on the edges between
are all equal to `ψ = φ_E(T w₁)`; (b) `ψ = ∅` iff `s₁` is a left and `s₂` a right side; (c) a
tile strictly between is a horizontal carrier iff `s₁` is a left and `s₂` a right side. The
vertical case is the same with `φ_S, φ_N` (apply this to the transposed column). -/
theorem routing {T : ℤ → RTile} {w1 w2 : ℤ} (hlt : w1 < w2)
    (hrule : ∀ x, w1 ≤ x → x ≤ w2 → FlowRules (T x).vw (T x).fW (T x).fE)
    (hmatch : ∀ x, w1 ≤ x → x < w2 → (T x).fE = (T (x + 1)).fW)
    {s1 s2 : Side} (h1 : (T w1).vw = some s1) (h2 : (T w2).vw = some s2)
    (hmid : ∀ x, w1 < x → x < w2 → (T x).vw = none) :
    (∀ x, w1 ≤ x → x < w2 → (T x).fE = (T w1).fE ∧ (T (x + 1)).fW = (T w1).fE) ∧
    ((T w1).fE = Flow.empty ↔ s1 = .lo ∧ s2 = .hi) ∧
    (∀ x, w1 < x → x < w2 → ((T x).HCarrier ↔ s1 = .lo ∧ s2 = .hi)) := by
  have ha : ∀ x, w1 ≤ x → x < w2 → (T x).fE = (T w1).fE ∧ (T (x + 1)).fW = (T w1).fE := by
    intro x hx hx2
    induction x, hx using Int.leInduction with
    | base => exact ⟨rfl, (hmatch w1 le_rfl hlt).symm⟩
    | succ x hx ih =>
      have ih := ih (by omega)
      have hr := hrule (x + 1) (by omega) (by omega)
      rw [hmid (x + 1) (by omega) hx2] at hr
      refine ⟨?_, ?_⟩
      · rw [← hr]; exact ih.2
      · rw [← hmatch (x + 1) (by omega) hx2, ← hr]; exact ih.2
  have hψ : (T w2).fW = (T w1).fE := by
    have := (ha (w2 - 1) (by omega) (by omega)).2
    rwa [sub_add_cancel] at this
  have hb : (T w1).fE = Flow.empty ↔ s1 = .lo ∧ s2 = .hi := by
    have r1 := hrule w1 le_rfl hlt.le
    have r2 := hrule w2 hlt.le le_rfl
    rw [h1] at r1; rw [h2, hψ] at r2
    generalize (T w1).fE = ψ at r1 r2
    obtain ⟨b1, b2⟩ := ψ
    cases s1 <;> cases s2 <;> cases b1 <;> cases b2 <;> simp_all [FlowRules, Flow.empty]
  refine ⟨ha, hb, fun x hx hx2 => ?_⟩
  have e1 := (ha x hx.le hx2).1
  have e2 := (ha (x - 1) (by omega) (by omega)).2
  rw [sub_add_cancel] at e2
  rw [RTile.HCarrier, e1, e2, and_self, hb]

/-! ## A routing on a line (the flows of `fam:positive`(a)) -/

section Line

variable (W : ℤ → Option Side) (hW : ∀ n : ℤ, ∃ k : ℕ, W (n - k) ≠ none)
  (hE : ∀ n : ℤ, ∃ k : ℕ, W (n + 1 + k) ≠ none)

/-- The nearest wall at or to the west of `e`. -/
noncomputable def westWall (e : ℤ) : ℤ := e - Nat.find (hW e)

/-- The nearest wall at or to the east of `e + 1`. -/
noncomputable def eastWall (e : ℤ) : ℤ := e + 1 + Nat.find (hE e)

variable {W hW hE}

theorem westWall_spec (e : ℤ) : W (westWall W hW e) ≠ none := Nat.find_spec (hW e)

theorem westWall_le (e : ℤ) : westWall W hW e ≤ e := by
  simp only [westWall]; omega

theorem westWall_max {e w : ℤ} (h1 : westWall W hW e < w) (h2 : w ≤ e) : W w = none := by
  have hk : (e - w).toNat < Nat.find (hW e) := by simp only [westWall] at h1; omega
  have := Nat.find_min (hW e) hk
  rw [show e - ((e - w).toNat : ℤ) = w by omega] at this
  simpa using this

theorem westWall_eq {e w : ℤ} (h1 : w ≤ e) (h2 : W w ≠ none) (h3 : ∀ w', w < w' → w' ≤ e → W w' = none) :
    westWall W hW e = w := by
  rcases lt_trichotomy (westWall W hW e) w with h | h | h
  · exact absurd (westWall_max h h1) h2
  · exact h
  · exact absurd (h3 _ h (westWall_le e)) (westWall_spec e)

theorem eastWall_spec (e : ℤ) : W (eastWall W hE e) ≠ none := Nat.find_spec (hE e)

theorem lt_eastWall (e : ℤ) : e < eastWall W hE e := by
  simp only [eastWall]; omega

theorem eastWall_min {e w : ℤ} (h1 : e < w) (h2 : w < eastWall W hE e) : W w = none := by
  have hk : (w - e - 1).toNat < Nat.find (hE e) := by simp only [eastWall] at h2; omega
  have := Nat.find_min (hE e) hk
  rw [show e + 1 + ((w - e - 1).toNat : ℤ) = w by omega] at this
  simpa using this

theorem eastWall_eq {e w : ℤ} (h1 : e < w) (h2 : W w ≠ none) (h3 : ∀ w', e < w' → w' < w → W w' = none) :
    eastWall W hE e = w := by
  rcases lt_trichotomy (eastWall W hE e) w with h | h | h
  · exact absurd (h3 _ (lt_eastWall e) h) (eastWall_spec e)
  · exact h
  · exact absurd (eastWall_min h1 h) h2

variable (W hW hE)

/-- `fam:positive`(a): the flow on the edge from `e` to `e + 1`: `∅` if the nearest walls are a
left side (west) and a right side (east), `{left}` if both are left sides, and `{right}` if the
western one is a right side. -/
noncomputable def lineFlow (e : ℤ) : Flow :=
  match W (westWall W hW e), W (eastWall W hE e) with
  | some .lo, some .hi => Flow.empty
  | some .lo, _ => (true, false)
  | _, _ => (false, true)

variable {W hW hE}

/-- `fam:positive`(a): the flows on the two edges of the site `x` obey the flow rules. -/
theorem lineFlow_rules (x : ℤ) : FlowRules (W x) (lineFlow W hW hE (x - 1)) (lineFlow W hW hE x) := by
  cases hx : W x with
  | none =>
    have hw : westWall W hW x = westWall W hW (x - 1) :=
      westWall_eq (by have := westWall_le (hW := hW) (x - 1); omega) (westWall_spec _)
        (fun w' h1 h2 => by
          rcases lt_or_eq_of_le h2 with h2 | rfl
          · exact westWall_max h1 (by omega)
          · exact hx)
    have he : eastWall W hE (x - 1) = eastWall W hE x :=
      eastWall_eq (by have := lt_eastWall (hE := hE) x; omega) (eastWall_spec _)
        (fun w' h1 h2 => by
          rcases lt_or_eq_of_le (show x ≤ w' by omega) with h3 | rfl
          · exact eastWall_min h3 h2
          · exact hx)
    simp only [FlowRules, lineFlow, hw, he]
  | some s =>
    have hw : westWall W hW x = x := westWall_eq le_rfl (by rw [hx]; simp) (fun _ h1 h2 => by omega)
    have he : eastWall W hE (x - 1) = x :=
      eastWall_eq (by omega) (by rw [hx]; simp) (fun _ h1 h2 => by omega)
    have hws := westWall_spec (hW := hW) (x - 1)
    have hes := eastWall_spec (hE := hE) x
    simp only [lineFlow, hw, he, hx]
    revert hws hes
    cases W (westWall W hW (x - 1)) <;> cases W (eastWall W hE x) <;> intro hws hes
    all_goals first
      | exact absurd rfl hws
      | exact absurd rfl hes
      | (rename_i a b; cases s <;> cases a <;> cases b <;> simp [FlowRules, Flow.empty])

end Line

/-! ## `fam:positive`(a): routing on the plane -/

section Positive

variable {f : ℕ → Plane → Letter}

/-- The light vertical walls along the row `z` of the quartering of `f_0`. -/
def rowWall (f : ℕ → Plane → Letter) (z x : ℤ) : Option Side := vWall (quad (x, z)) (f 0 (half (x, z)))

/-- The light horizontal walls along the column `x` of the quartering of `f_0`. -/
def colWall (f : ℕ → Plane → Letter) (x y : ℤ) : Option Side := hWall (quad (x, y)) (f 0 (half (x, y)))

/-- `fam:walls` on the plane, for a tower of height `∞` with phase `(1/3, 1/3)` (every column has a
finite rank). -/
theorem rowWall_iff (hf : IsInfTower (diag third) f) (z x : ℤ) (s : Side) :
    rowWall f z x = some s ↔ ∃ d, 1 ≤ d ∧
      ((s = .lo ∧ IsLeftEnd (towerOffsets third) d x) ∨
        (s = .hi ∧ IsRightEnd (towerOffsets third) d x)) ∧ InFrame (towerOffsets third) d z := by
  obtain ⟨r, hr⟩ := exists_rank_third (x / 2)
  exact walls_col (hf.towerRel (r + 2)) (towerOffsets_spec third) (ξ := (x, z)) hr le_rfl s

theorem colWall_iff (hf : IsInfTower (diag third) f) (x y : ℤ) (s : Side) :
    colWall f x y = some s ↔ ∃ d, 1 ≤ d ∧
      ((s = .lo ∧ IsLeftEnd (towerOffsets third) d y) ∨
        (s = .hi ∧ IsRightEnd (towerOffsets third) d y)) ∧ InFrame (towerOffsets third) d x := by
  obtain ⟨r, hr⟩ := exists_rank_third (y / 2)
  exact walls_row (hf.towerRel (r + 2)) (towerOffsets_spec third) (ξ := (x, y)) hr le_rfl s

/-- Left endpoints of depth `d` far to the west and to the east of any `n`. -/
theorem exists_frameLo_le (a : ℕ → ℤ) (d : ℕ) (n : ℤ) : ∃ m, frameLo a d m ≤ n := by
  have hp : (1 : ℤ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
  refine ⟨-(|n| + |a d| + 1), ?_⟩
  simp only [frameLo]
  have := neg_abs_le n; have := le_abs_self (a d); have := abs_nonneg n; have := abs_nonneg (a d)
  have := mul_nonneg (show (0 : ℤ) ≤ 4 * (|n| + |a d| + 1) - 1 by linarith)
    (show (0 : ℤ) ≤ 4 ^ d - 1 by linarith)
  nlinarith

theorem exists_le_frameLo (a : ℕ → ℤ) (d : ℕ) (n : ℤ) : ∃ m, n ≤ frameLo a d m := by
  have hp : (1 : ℤ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
  refine ⟨|n| + |a d| + 1, ?_⟩
  simp only [frameLo]
  have := le_abs_self n; have := neg_abs_le (a d); have := abs_nonneg n; have := abs_nonneg (a d)
  have := mul_nonneg (show (0 : ℤ) ≤ 4 * (|n| + |a d| + 1) + 1 by linarith)
    (show (0 : ℤ) ≤ 4 ^ d - 1 by linarith)
  nlinarith

/-- `fam:positive` (proof): the frames of depth `own(z)` are unbounded in both directions, so the
row `z` has light vertical walls arbitrarily far to the west. -/
theorem rowWall_west (hf : IsInfTower (diag third) f) (z n : ℤ) :
    ∃ k : ℕ, rowWall f z (n - k) ≠ none := by
  obtain ⟨hd, hz⟩ := own_spec _ forall_inFrame_third z
  obtain ⟨m, hm⟩ := exists_frameLo_le (towerOffsets third) (own _ forall_inFrame_third z) n
  refine ⟨(n - frameLo (towerOffsets third) (own _ forall_inFrame_third z) m).toNat, ?_⟩
  rw [show n - ((n - frameLo (towerOffsets third) (own _ forall_inFrame_third z) m).toNat : ℤ) =
    frameLo (towerOffsets third) (own _ forall_inFrame_third z) m by omega]
  intro h
  have := (rowWall_iff hf z _ .lo).2 ⟨_, hd, Or.inl ⟨rfl, m, rfl⟩, hz⟩
  rw [h] at this; cases this

theorem rowWall_east (hf : IsInfTower (diag third) f) (z n : ℤ) :
    ∃ k : ℕ, rowWall f z (n + 1 + k) ≠ none := by
  obtain ⟨hd, hz⟩ := own_spec _ forall_inFrame_third z
  obtain ⟨m, hm⟩ := exists_le_frameLo (towerOffsets third) (own _ forall_inFrame_third z) (n + 1)
  refine ⟨(frameLo (towerOffsets third) (own _ forall_inFrame_third z) m - (n + 1)).toNat, ?_⟩
  rw [show n + 1 + ((frameLo (towerOffsets third) (own _ forall_inFrame_third z) m - (n + 1)).toNat : ℤ) =
    frameLo (towerOffsets third) (own _ forall_inFrame_third z) m by omega]
  intro h
  have := (rowWall_iff hf z _ .lo).2 ⟨_, hd, Or.inl ⟨rfl, m, rfl⟩, hz⟩
  rw [h] at this; cases this

theorem colWall_south (hf : IsInfTower (diag third) f) (x n : ℤ) :
    ∃ k : ℕ, colWall f x (n - k) ≠ none := by
  obtain ⟨hd, hx⟩ := own_spec _ forall_inFrame_third x
  obtain ⟨m, hm⟩ := exists_frameLo_le (towerOffsets third) (own _ forall_inFrame_third x) n
  refine ⟨(n - frameLo (towerOffsets third) (own _ forall_inFrame_third x) m).toNat, ?_⟩
  rw [show n - ((n - frameLo (towerOffsets third) (own _ forall_inFrame_third x) m).toNat : ℤ) =
    frameLo (towerOffsets third) (own _ forall_inFrame_third x) m by omega]
  intro h
  have := (colWall_iff hf x _ .lo).2 ⟨_, hd, Or.inl ⟨rfl, m, rfl⟩, hx⟩
  rw [h] at this; cases this

theorem colWall_north (hf : IsInfTower (diag third) f) (x n : ℤ) :
    ∃ k : ℕ, colWall f x (n + 1 + k) ≠ none := by
  obtain ⟨hd, hx⟩ := own_spec _ forall_inFrame_third x
  obtain ⟨m, hm⟩ := exists_le_frameLo (towerOffsets third) (own _ forall_inFrame_third x) (n + 1)
  refine ⟨(frameLo (towerOffsets third) (own _ forall_inFrame_third x) m - (n + 1)).toNat, ?_⟩
  rw [show n + 1 + ((frameLo (towerOffsets third) (own _ forall_inFrame_third x) m - (n + 1)).toNat : ℤ) =
    frameLo (towerOffsets third) (own _ forall_inFrame_third x) m by omega]
  intro h
  have := (colWall_iff hf x _ .lo).2 ⟨_, hd, Or.inl ⟨rfl, m, rfl⟩, hx⟩
  rw [h] at this; cases this

/-- `fam:positive`(a): the routed tiling `ϑ`: the quartering of `f_0`, with the flows of the
nearest walls along each row (east, west) and each column (north, south). -/
noncomputable def routedTiling (hf : IsInfTower (diag third) f) (ξ : Plane) : RTile :=
  ⟨quarter (f 0) ξ,
    lineFlow (rowWall f ξ.2) (rowWall_west hf ξ.2) (rowWall_east hf ξ.2) (ξ.1 - 1),
    lineFlow (rowWall f ξ.2) (rowWall_west hf ξ.2) (rowWall_east hf ξ.2) ξ.1,
    lineFlow (colWall f ξ.1) (colWall_south hf ξ.1) (colWall_north hf ξ.1) (ξ.2 - 1),
    lineFlow (colWall f ξ.1) (colWall_south hf ξ.1) (colWall_north hf ξ.1) ξ.2⟩

/-- **`fam:positive`(a).** Let `(f_m)` be a tower of height `∞` with phase `(1/3, 1/3)`. There are
flows on the edges of `ℤ²` such that `f_0^q` together with these flows is a tiling of `𝔸^r`. -/
theorem positive_a (hf : IsInfTower (diag third) f) :
    (∀ ξ, (routedTiling hf ξ).q = quarter (f 0) ξ) ∧ (∀ ξ, (routedTiling hf ξ).InR) ∧
      LegalOn RTile.MatchE RTile.MatchN Set.univ (routedTiling hf) := by
  have hq := (hf.tiling 0).quarter
  refine ⟨fun ξ => rfl, fun ξ => ⟨hq.1 ξ,
      lineFlow_rules (W := rowWall f ξ.2) (hW := rowWall_west hf ξ.2) (hE := rowWall_east hf ξ.2) ξ.1,
      lineFlow_rules (W := colWall f ξ.1) (hW := colWall_south hf ξ.1) (hE := colWall_north hf ξ.1)
        ξ.2⟩,
    fun ξ _ _ => ⟨hq.2.1 ξ trivial trivial, ?_⟩, fun ξ _ _ => ⟨hq.2.2 ξ trivial trivial, ?_⟩⟩
  · obtain ⟨x, z⟩ := ξ
    simp only [routedTiling, Prod.mk_add_mk, add_zero, add_sub_cancel_right]
  · obtain ⟨x, z⟩ := ξ
    simp only [routedTiling, Prod.mk_add_mk, add_zero, add_sub_cancel_right]

end Positive

end FNE.Family
