/-
# Section 6.7: the family `R_M` (`def:family`) and `prop:tiles`

* `def:family`: a tile of `R_M` is a tile of `𝔸^r` with a payload in the palette of its role
  (`FTile`, `palette`, `FTile.InR`). Its colour on a side is the pair of the `𝔸^r` colour and the
  payload colour, coded into `ℕ` injectively (`FTile.toTile`: `Nat.pair` of the `Encodable` code
  of the `𝔸^r` colour and the code `colCode` of the payload colour, `Family/Codes.lean`),
  so that `R_M` is a `List Tile` (`familyR`): the codes of the members of an explicit finite list
  of candidates (`ftileList`: quadrants × the 276 letters × flows × payloads with colours in
  `C_M`), filtered by membership.
* **`prop:tiles`** (`tiles_of_not_halts`): if `M` does not halt, `R_M` tiles. As printed: a tower
  of phase `(1/3, 1/3)`, the routed tiling of `fam:positive`(a), the tiling `Υ` of
  `prop:horn`(b), addresses, payloads by role (fixed and free sides), palettes, matching.

**[choice]** `familyR` is defined with classical decidability of membership (the active palette
`T_M` is a `Prop`); the list of candidates is explicit. `Computable familyR` is proved in
`Family/Computable.lean` (a decidable form of each palette on the candidates, and `Primrec`
plumbing over the explicit lists).
-/
import FixedNoiseErgodicity.Family.Free
import FixedNoiseErgodicity.Family.Codes
import Mathlib.Tactic.DeriveEncodable

set_option autoImplicit false

namespace FNE.Family

open FNE FNE.Scaffold

deriving instance Encodable for VAtom, HAtom, Thin, Corner, Thick, Black, Formal, Letter, HCol,
  VCol

/-! ## `def:family` -/

/-- `def:family`: the palette of a role: inactive `C_M^4`; horizontal `{𝐜_W = 𝐜_E}`; vertical
`{𝐜_S = 𝐜_N}`; active `T_M`; seed `{s_M}`. (Colours of `C_M` are the sets with sites in `Λ` and
facts in `ℋ_M`, `InC`.) -/
def palette (M : TuringMachine) : Role → Pay → Prop
  | .inactive, c => InC M c.W ∧ InC M c.E ∧ InC M c.S ∧ InC M c.N
  | .horiz, c => (InC M c.W ∧ InC M c.E ∧ InC M c.S ∧ InC M c.N) ∧ c.W = c.E
  | .vert, c => (InC M c.W ∧ InC M c.E ∧ InC M c.S ∧ InC M c.N) ∧ c.S = c.N
  | .active, c => InT M c
  | .seed, c => c = seedTile M

/-- `def:family`: a candidate tile `ϑ = (quad, par, φ_W, φ_E, φ_S, φ_N, pay)`: a routed tile
and a payload. -/
structure FTile where
  /-- the `𝔸^r` part -/
  r : RTile
  /-- the payload -/
  pay : Pay

/-- `def:family`: `ϑ ∈ R_M`: the `𝔸^r` part is a tile of `𝔸^r` and the payload lies in the
palette of its role. -/
def FTile.InR (M : TuringMachine) (t : FTile) : Prop := t.r.InR ∧ palette M t.r.role t.pay

/-- `def:family`: the colour of `ϑ` on a side is the pair of the colour of its `𝔸^r` tile on that
side (scaffold-pair colour and flow) and the payload colour, coded into `ℕ` injectively.
**[choice]** The payload colour is coded by `colCode` (`Family/Codes.lean`). -/
def FTile.toTile (t : FTile) : Tile :=
  ⟨Nat.pair (Encodable.encode (t.r.q.colN, t.r.fN)) (colCode t.pay.N),
    Nat.pair (Encodable.encode (t.r.q.colE, t.r.fE)) (colCode t.pay.E),
    Nat.pair (Encodable.encode (t.r.q.colS, t.r.fS)) (colCode t.pay.S),
    Nat.pair (Encodable.encode (t.r.q.colW, t.r.fW)) (colCode t.pay.W)⟩

theorem FTile.toTile_E_W {t t' : FTile} (hq : t.r.q.colE = t'.r.q.colW) (hf : t.r.fE = t'.r.fW)
    (hp : t.pay.E = t'.pay.W) : t.toTile.E = t'.toTile.W := by
  simp [FTile.toTile, hq, hf, hp]

theorem FTile.toTile_N_S {t t' : FTile} (hq : t.r.q.colN = t'.r.q.colS) (hf : t.r.fN = t'.r.fS)
    (hp : t.pay.N = t'.pay.S) : t.toTile.N = t'.toTile.S := by
  simp [FTile.toTile, hq, hf, hp]

/-- Matching of coded tiles is matching of the parts (the codes are injective). -/
theorem FTile.toTile_E_W_iff (t t' : FTile) :
    t.toTile.E = t'.toTile.W ↔
      t.r.q.colE = t'.r.q.colW ∧ t.r.fE = t'.r.fW ∧ t.pay.E = t'.pay.W := by
  simp only [FTile.toTile, Nat.pair_eq_pair, Encodable.encode_inj, colCode_injective.eq_iff,
    Prod.mk.injEq, and_assoc]

theorem FTile.toTile_N_S_iff (t t' : FTile) :
    t.toTile.N = t'.toTile.S ↔
      t.r.q.colN = t'.r.q.colS ∧ t.r.fN = t'.r.fS ∧ t.pay.N = t'.pay.S := by
  simp only [FTile.toTile, Nat.pair_eq_pair, Encodable.encode_inj, colCode_injective.eq_iff,
    Prod.mk.injEq, and_assoc]

/-! ## The list of candidates -/

/-- The symbols of `M°` below `B`. -/
def osymList (B : ℕ) : List OSym :=
  (List.range B).flatMap fun u => (List.range B).flatMap fun v => [⟨false, u, v⟩, ⟨true, u, v⟩]

theorem mem_osymList {B : ℕ} {γ : OSym} : γ ∈ osymList B ↔ SymOK B γ := by
  obtain ⟨m, u, v⟩ := γ
  simp only [osymList, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false, OSym.mk.injEq, SymOK]
  constructor
  · rintro ⟨a, ha, b, hb, ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩ <;> exact ⟨ha, hb⟩
  · rintro ⟨hu, hv⟩; exact ⟨u, hu, v, hv, by cases m <;> simp⟩

/-- The states of `M°` below `B`. -/
def ostateList (B : ℕ) : List OState :=
  .init :: (List.range B).flatMap fun q => [.sim q false, .sim q true, .back q false, .back q true]

theorem mem_ostateList {B : ℕ} {q : OState} : q ∈ ostateList B ↔ StOK B q := by
  cases q with
  | init => simp [ostateList, StOK]
  | sim q l =>
    simp only [ostateList, List.mem_cons, List.mem_flatMap, List.mem_range, reduceCtorEq,
      false_or, StOK, OState.sim.injEq, OState.back.injEq, and_false, or_false,
      List.not_mem_nil]
    constructor
    · rintro ⟨a, ha, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ <;> exact ha
    · intro h; exact ⟨q, h, by cases l <;> simp⟩
  | back q l =>
    simp only [ostateList, List.mem_cons, List.mem_flatMap, List.mem_range, reduceCtorEq,
      false_or, StOK, OState.sim.injEq, OState.back.injEq, and_false, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨a, ha, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ <;> exact ha
    · intro h; exact ⟨q, h, by cases l <;> simp⟩

/-- `𝒮_M` as a list. -/
def sList (B : ℕ) : List MSym :=
  .wall :: ((osymList B).map .tape ++ (ostateList B).flatMap fun q => (osymList B).map (.head q))

theorem mem_sList {B : ℕ} {b : MSym} : b ∈ sList B ↔ InS B b := by
  cases b with
  | wall => simp [sList, InS]
  | tape γ =>
    simp [sList, InS, mem_osymList]
  | head q γ =>
    simp [sList, InS, mem_osymList, mem_ostateList]

/-- `ℋ_M` as a list. -/
def hList (M : TuringMachine) : List Fact :=
  .seed :: .start :: .ray :: (sList (bnd M)).map .P

theorem mem_hList {M : TuringMachine} {F : Fact} : F ∈ hList M ↔ InH M F := by
  cases F with
  | P b => simp [hList, InH, mem_sList]
  | _ => simp [hList, InH]

/-- `Λ` as a list. -/
def lamList : List Plane := [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)]

theorem mem_lamList {y : Plane} : y ∈ lamList ↔ y ∈ box 1 := by
  rw [← lam_eq]
  simp [lamList, lam]

/-- `𝒰_M = {h, v} × Λ × ℋ_M` as a list. -/
def uList (M : TuringMachine) : List (Bool × Plane × Fact) :=
  [false, true].flatMap fun b => lamList.flatMap fun y => (hList M).map fun F => (b, y, F)

theorem mem_uList {M : TuringMachine} {x : Bool × Plane × Fact} :
    x ∈ uList M ↔ x.2.1 ∈ box 1 ∧ InH M x.2.2 := by
  obtain ⟨b, y, F⟩ := x
  simp only [uList, List.mem_flatMap, List.mem_map, mem_lamList, mem_hList, Prod.mk.injEq]
  constructor
  · rintro ⟨b', -, y', hy, F', hF, rfl, rfl, rfl⟩; exact ⟨hy, hF⟩
  · rintro ⟨hy, hF⟩; exact ⟨b, by cases b <;> simp, y, hy, F, hF, rfl, rfl, rfl⟩

/-- `C_M` as a list (all subsets of `𝒰_M`). -/
def colourList (M : TuringMachine) : List Colour := (uList M).sublists.map List.toFinset

theorem mem_colourList {M : TuringMachine} {c : Colour} (h : InC M c) : c ∈ colourList M := by
  refine List.mem_map.2 ⟨(uList M).filter (· ∈ c), List.mem_sublists.2 List.filter_sublist, ?_⟩
  ext x
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun hx => ⟨mem_uList.2 (h x hx), hx⟩⟩

/-- `C_M^4` as a list. -/
def payList (M : TuringMachine) : List Pay :=
  (colourList M).flatMap fun w => (colourList M).flatMap fun e => (colourList M).flatMap fun s =>
    (colourList M).map fun n => ⟨w, e, s, n⟩

theorem mem_payList {M : TuringMachine} {c : Pay}
    (h : InC M c.W ∧ InC M c.E ∧ InC M c.S ∧ InC M c.N) : c ∈ payList M := by
  simp only [payList, List.mem_flatMap, List.mem_map]
  exact ⟨c.W, mem_colourList h.1, c.E, mem_colourList h.2.1, c.S, mem_colourList h.2.2.1, c.N,
    mem_colourList h.2.2.2, rfl⟩

/-- The four flows. -/
def flowList : List Flow := [(false, false), (false, true), (true, false), (true, true)]

theorem mem_flowList (φ : Flow) : φ ∈ flowList := by
  obtain ⟨a, b⟩ := φ; cases a <;> cases b <;> simp [flowList]

/-- Candidate routed tiles: a quadrant, a letter of `𝔸`, four flows. -/
def rtileList : List RTile :=
  flowList.flatMap fun s => Letter.letters.flatMap fun a => flowList.flatMap fun w =>
    flowList.flatMap fun e => flowList.flatMap fun so => flowList.map fun n => ⟨⟨s, a⟩, w, e, so, n⟩

theorem mem_rtileList {t : RTile} (h : t.InR) : t ∈ rtileList := by
  obtain ⟨⟨s, a⟩, w, e, so, n⟩ := t
  simp only [rtileList, List.mem_flatMap, List.mem_map]
  exact ⟨s, mem_flowList s, a, Letter.mem_letters.2 h.1, w, mem_flowList w, e, mem_flowList e,
    so, mem_flowList so, n, mem_flowList n, rfl⟩

/-- The candidates for `R_M`. -/
def ftileList (M : TuringMachine) : List FTile :=
  rtileList.flatMap fun r => (payList M).map fun p => ⟨r, p⟩

/-- The colours of every payload in a palette lie in `C_M`. -/
theorem palette_inC {M : TuringMachine} {ρ : Role} {c : Pay} (h : palette M ρ c) :
    InC M c.W ∧ InC M c.E ∧ InC M c.S ∧ InC M c.N := by
  cases ρ with
  | inactive => exact h
  | horiz => exact h.1
  | vert => exact h.1
  | active => exact h.inC
  | seed => rw [show c = seedTile M from h]; exact (seedTile_inT M).inC

theorem mem_ftileList {M : TuringMachine} {t : FTile} (h : t.InR M) : t ∈ ftileList M := by
  obtain ⟨r, p⟩ := t
  simp only [ftileList, List.mem_flatMap, List.mem_map]
  exact ⟨r, mem_rtileList h.1, p, mem_payList (palette_inC h.2), rfl⟩

open Classical in
/-- **`def:family`.** The Wang set `R_M`, as a list of tiles: the codes of the candidates that lie
in `R_M`. -/
noncomputable def familyR (M : TuringMachine) : List Tile :=
  ((ftileList M).filter fun t => decide (t.InR M)).map FTile.toTile

theorem toTile_mem_familyR {M : TuringMachine} {t : FTile} (h : t.InR M) :
    t.toTile ∈ familyR M := by
  classical
  exact List.mem_map.2 ⟨t, List.mem_filter.2 ⟨mem_ftileList h, decide_eq_true h⟩, rfl⟩

/-! ## `prop:tiles` -/

section Tiles

variable (M : TuringMachine) (ϑ : Plane → RTile) (Υ : Plane → Pay)

/-- `z` is a free coordinate at its own depth (`z ∈ 𝓕_{own(z)}(m)` for some `m`). -/
def FreeOwn (z : ℤ) : Prop := ∃ m, IsFree (towerOffsets third) (own _ forall_inFrame_third z) m z

/-- The address pair of a horizontal carrier (and of an active tile): both coordinates at the
depth `own(ξ₂)`. -/
noncomputable def pH (ξ : Plane) : Plane :=
  (adr (towerOffsets third) (own _ forall_inFrame_third ξ.2) ξ.1,
    adr (towerOffsets third) (own _ forall_inFrame_third ξ.2) ξ.2)

/-- The address pair of a vertical carrier: both coordinates at the depth `own(ξ₁)`. -/
noncomputable def pV (ξ : Plane) : Plane :=
  (adr (towerOffsets third) (own _ forall_inFrame_third ξ.1) ξ.1,
    adr (towerOffsets third) (own _ forall_inFrame_third ξ.1) ξ.2)

open Classical in
/-- `prop:tiles`, payloads: the fixed west side (of a horizontal carrier): `Υ(ad ξ₁, ad ξ₂)_W` if
active, `Υ(ad⁻ ξ₁, ad ξ₂)_E` if horizontal on a free row, `∅` otherwise. -/
noncomputable def fixW (ξ : Plane) : Colour :=
  if (ϑ ξ).VCarrier then (Υ (pH ξ)).W else if FreeOwn ξ.2 then (Υ (pH ξ)).E else ∅

open Classical in
/-- The fixed east side (of a horizontal carrier). -/
noncomputable def fixE (ξ : Plane) : Colour :=
  if (ϑ ξ).VCarrier then (Υ (pH ξ)).E else if FreeOwn ξ.2 then (Υ (pH ξ)).E else ∅

open Classical in
/-- The fixed south side (of a vertical carrier). -/
noncomputable def fixS (ξ : Plane) : Colour :=
  if (ϑ ξ).HCarrier then (Υ (pV ξ)).S else if FreeOwn ξ.1 then (Υ (pV ξ)).N else ∅

open Classical in
/-- The fixed north side (of a vertical carrier). -/
noncomputable def fixN (ξ : Plane) : Colour :=
  if (ϑ ξ).HCarrier then (Υ (pV ξ)).N else if FreeOwn ξ.1 then (Υ (pV ξ)).N else ∅

/-- `prop:tiles`, payloads: fixed sides as above; a free side copies the facing side across its
edge if that side is fixed, and is `∅` otherwise. -/
noncomputable def payOf (ξ : Plane) : Pay :=
  ⟨if (ϑ ξ).HCarrier then fixW ϑ Υ ξ
    else if (ϑ (ξ - (1, 0))).HCarrier then fixE ϑ Υ (ξ - (1, 0)) else ∅,
   if (ϑ ξ).HCarrier then fixE ϑ Υ ξ
    else if (ϑ (ξ + (1, 0))).HCarrier then fixW ϑ Υ (ξ + (1, 0)) else ∅,
   if (ϑ ξ).VCarrier then fixS ϑ Υ ξ
    else if (ϑ (ξ - (0, 1))).VCarrier then fixN ϑ Υ (ξ - (0, 1)) else ∅,
   if (ϑ ξ).VCarrier then fixN ϑ Υ ξ
    else if (ϑ (ξ + (0, 1))).VCarrier then fixS ϑ Υ (ξ + (0, 1)) else ∅⟩

variable {M ϑ Υ}

theorem inC_empty : InC M ∅ := fun _ h => absurd h (Finset.notMem_empty _)

variable (hΥ : ∀ u, InT M (Υ u))
include hΥ

theorem inC_fix (ξ : Plane) : InC M (fixW ϑ Υ ξ) ∧ InC M (fixE ϑ Υ ξ) ∧
    InC M (fixS ϑ Υ ξ) ∧ InC M (fixN ϑ Υ ξ) := by
  have hU : ∀ u, InC M (Υ u).W ∧ InC M (Υ u).E ∧ InC M (Υ u).S ∧ InC M (Υ u).N :=
    fun u => (hΥ u).inC
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [fixW, fixE, fixS, fixN] <;> split_ifs
  all_goals first
    | exact inC_empty
    | exact (hU _).1
    | exact (hU _).2.1
    | exact (hU _).2.2.1
    | exact (hU _).2.2.2

theorem inC_payOf (ξ : Plane) : InC M (payOf ϑ Υ ξ).W ∧ InC M (payOf ϑ Υ ξ).E ∧
    InC M (payOf ϑ Υ ξ).S ∧ InC M (payOf ϑ Υ ξ).N := by
  have hF := inC_fix hΥ (ϑ := ϑ)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [payOf] <;> split_ifs
  all_goals first
    | exact inC_empty
    | exact (hF _).1
    | exact (hF _).2.1
    | exact (hF _).2.2.1
    | exact (hF _).2.2.2

omit hΥ

variable {f : ℕ → Plane → Letter} (hf : IsInfTower (diag third) f)
  (hq : ∀ ξ, (ϑ ξ).q = quarter (f 0) ξ) (hR : ∀ ξ, (ϑ ξ).InR)
  (hL : LegalOn RTile.MatchE RTile.MatchN Set.univ ϑ)
include hf hq hR hL

/-- An active tile has `own(ξ₁) = own(ξ₂)`, so its two address pairs agree. -/
theorem pH_eq_pV {ξ : Plane} (hH : (ϑ ξ).HCarrier) (hV : (ϑ ξ).VCarrier) : pH ξ = pV ξ := by
  obtain ⟨d, m, m', hd, h1, h2⟩ := (positive_c hf hq hR hL ξ).1 ⟨hH, hV⟩
  rw [isFree_iff_own hd] at h1 h2
  simp only [pH, pV, h1.2.2, h2.2.2]

/-- A vertical carrier that is also a horizontal carrier lies on a free row. -/
theorem freeOwn_of_active {ξ : Plane} (hH : (ϑ ξ).HCarrier) (hV : (ϑ ξ).VCarrier) :
    FreeOwn ξ.1 ∧ FreeOwn ξ.2 := by
  obtain ⟨d, m, m', hd, h1, h2⟩ := (positive_c hf hq hR hL ξ).1 ⟨hH, hV⟩
  have e1 := ((isFree_iff_own hd).1 h1).2.2
  have e2 := ((isFree_iff_own hd).1 h2).2.2
  exact ⟨⟨m, by rw [e1]; exact h1⟩, ⟨m', by rw [e2]; exact h2⟩⟩

/-- On a horizontal carrier in a free row, the tile is a vertical carrier iff `ξ₁` is free at the
depth of the row. -/
theorem vCarrier_iff {ξ : Plane} (hH : (ϑ ξ).HCarrier) (hz : FreeOwn ξ.2) {m : ℤ}
    (hm : frameLo (towerOffsets third) (own _ forall_inFrame_third ξ.2) m < ξ.1 ∧
      ξ.1 < frameHi (towerOffsets third) (own _ forall_inFrame_third ξ.2) m) :
    (ϑ ξ).VCarrier ↔ IsFree (towerOffsets third) (own _ forall_inFrame_third ξ.2) m ξ.1 := by
  obtain ⟨m'', hz⟩ := hz
  have hd := (own_spec _ forall_inFrame_third ξ.2).1
  constructor
  · intro hV
    obtain ⟨d, m1, m2, hd', h1, h2⟩ := (positive_c hf hq hR hL ξ).1 ⟨hH, hV⟩
    have e2 := ((isFree_iff_own hd').1 h2).2.2
    subst e2
    have := frame_window_unique ⟨h1.1.le, h1.2.1.le⟩ ⟨hm.1.le, hm.2.le⟩
    subst this; exact h1
  · intro h
    exact ((positive_c hf hq hR hL ξ).2 ⟨_, m, m'', hd, h, hz⟩).2

/-- On a vertical carrier in a free column, the tile is a horizontal carrier iff `ξ₂` is free at
the depth of the column. -/
theorem hCarrier_iff {ξ : Plane} (hV : (ϑ ξ).VCarrier) (hx : FreeOwn ξ.1) {m : ℤ}
    (hm : frameLo (towerOffsets third) (own _ forall_inFrame_third ξ.1) m < ξ.2 ∧
      ξ.2 < frameHi (towerOffsets third) (own _ forall_inFrame_third ξ.1) m) :
    (ϑ ξ).HCarrier ↔ IsFree (towerOffsets third) (own _ forall_inFrame_third ξ.1) m ξ.2 := by
  obtain ⟨m'', hx⟩ := hx
  have hd := (own_spec _ forall_inFrame_third ξ.1).1
  constructor
  · intro hH
    obtain ⟨d, m1, m2, hd', h1, h2⟩ := (positive_c hf hq hR hL ξ).1 ⟨hH, hV⟩
    have e1 := ((isFree_iff_own hd').1 h1).2.2
    subst e1
    have := frame_window_unique ⟨h2.1.le, h2.2.1.le⟩ ⟨hm.1.le, hm.2.le⟩
    subst this; exact h2
  · intro h
    exact ((positive_c hf hq hR hL ξ).2 ⟨_, m'', m, hd, hx, h⟩).1

/-- `prop:tiles`, matching, the main case: two horizontal carriers side by side. -/
theorem fixE_eq_fixW (hΥE : ∀ u, (Υ u).E = (Υ (u + (1, 0))).W) {ξ : Plane}
    (h1 : (ϑ ξ).HCarrier) (h2 : (ϑ (ξ + (1, 0))).HCarrier) :
    fixE ϑ Υ ξ = fixW ϑ Υ (ξ + (1, 0)) := by
  obtain ⟨x, z⟩ := ξ
  have e : ((x, z) + (1, 0) : Plane) = (x + 1, z) := by simp
  rw [e] at h2 ⊢
  obtain ⟨m, hm1, hm2⟩ := (positive_b_row_all hf hq hR hL (x, z)).1 h1
  obtain ⟨m', hm1', hm2'⟩ := (positive_b_row_all hf hq hR hL (x + 1, z)).1 h2
  simp only at hm1 hm2 hm1' hm2'
  have hmm : m' = m := frame_window_unique ⟨hm1'.le, hm2'.le⟩ ⟨by omega, by omega⟩
  subst hmm
  by_cases hz : FreeOwn z
  · have hstep := adr_succ (a := towerOffsets third) (d := own _ forall_inFrame_third z)
      (m := m') (z := x) hm1.le (by omega)
    have hE : fixE ϑ Υ (x, z) = (Υ (pH (x, z))).E := by
      simp only [fixE]; split_ifs <;> simp_all
    rw [hE]
    have hv := vCarrier_iff hf hq hR hL h2 hz (m := m') ⟨hm1', hm2'⟩
    simp only [fixW, pH] at hv ⊢
    simp only [pH] at hE ⊢
    by_cases hfree : IsFree (towerOffsets third) (own _ forall_inFrame_third z) m' (x + 1)
    · rw [if_pos (hv.2 hfree), hstep, if_pos hfree, hΥE]
      simp
    · rw [if_neg (fun h => hfree (hv.1 h)), if_pos hz, hstep, if_neg hfree, add_zero]
  · have hv1 : ¬ (ϑ (x, z)).VCarrier := fun hV => hz (freeOwn_of_active hf hq hR hL h1 hV).2
    have hv2 : ¬ (ϑ (x + 1, z)).VCarrier := fun hV =>
      hz (freeOwn_of_active hf hq hR hL h2 hV).2
    simp only [fixE, fixW, hv1, hv2, hz, if_false]

/-- `prop:tiles`, matching, the main case: two vertical carriers one above the other. -/
theorem fixN_eq_fixS (hΥN : ∀ u, (Υ u).N = (Υ (u + (0, 1))).S) {ξ : Plane}
    (h1 : (ϑ ξ).VCarrier) (h2 : (ϑ (ξ + (0, 1))).VCarrier) :
    fixN ϑ Υ ξ = fixS ϑ Υ (ξ + (0, 1)) := by
  obtain ⟨x, z⟩ := ξ
  have e : ((x, z) + (0, 1) : Plane) = (x, z + 1) := by simp
  rw [e] at h2 ⊢
  obtain ⟨m, hm1, hm2⟩ := (positive_b_col_all hf hq hR hL (x, z)).1 h1
  obtain ⟨m', hm1', hm2'⟩ := (positive_b_col_all hf hq hR hL (x, z + 1)).1 h2
  simp only at hm1 hm2 hm1' hm2'
  have hmm : m' = m := frame_window_unique ⟨hm1'.le, hm2'.le⟩ ⟨by omega, by omega⟩
  subst hmm
  by_cases hx : FreeOwn x
  · have hstep := adr_succ (a := towerOffsets third) (d := own _ forall_inFrame_third x)
      (m := m') (z := z) hm1.le (by omega)
    have hN : fixN ϑ Υ (x, z) = (Υ (pV (x, z))).N := by
      simp only [fixN]; split_ifs <;> simp_all
    rw [hN]
    have hh := hCarrier_iff hf hq hR hL h2 hx (m := m') ⟨hm1', hm2'⟩
    simp only [fixS, pV] at hh ⊢
    by_cases hfree : IsFree (towerOffsets third) (own _ forall_inFrame_third x) m' (z + 1)
    · rw [if_pos (hh.2 hfree), hstep, if_pos hfree, hΥN]
      simp
    · rw [if_neg (fun h => hfree (hh.1 h)), if_pos hx, hstep, if_neg hfree, add_zero]
  · have hh1 : ¬ (ϑ (x, z)).HCarrier := fun hH => hx (freeOwn_of_active hf hq hR hL hH h1).1
    have hh2 : ¬ (ϑ (x, z + 1)).HCarrier := fun hH =>
      hx (freeOwn_of_active hf hq hR hL hH h2).1
    simp only [fixN, fixS, hh1, hh2, hx, if_false]

/-- `prop:tiles`, palettes: the payload of `ξ` lies in the palette of the role of `ϑ(ξ)`. -/
theorem payOf_palette (hΥ : ∀ u, InT M (Υ u)) (hΥ0 : Υ (0, 0) = seedTile M) (ξ : Plane) :
    palette M (ϑ ξ).role (payOf ϑ Υ ξ) := by
  have hC := inC_payOf hΥ (ϑ := ϑ) ξ
  unfold RTile.role
  by_cases hH : (ϑ ξ).HCarrier <;> by_cases hV : (ϑ ξ).VCarrier
  · have hpay : payOf ϑ Υ ξ = Υ (pH ξ) := by
      have e := pH_eq_pV hf hq hR hL hH hV
      ext1 <;> simp [payOf, fixW, fixE, fixS, fixN, hH, hV, e]
    rw [if_pos ⟨hH, hV⟩]
    split_ifs with hs
    · -- the seed: at a pair of centres, where the addresses are `0`
      show payOf ϑ Υ ξ = seedTile M
      rw [hpay, ← hΥ0]
      obtain ⟨d, m, m', hd, rfl⟩ := seed_at_centres hf (by rw [← hq]; exact hs)
      have ho : own _ forall_inFrame_third (cen (towerOffsets third) d m') = d :=
        ((isFree_iff_own hd).1 (cen_free (frameOffsets_tower third) hd m')).2.2
      simp only [pH, ho, adr_cen]
    · show InT M (payOf ϑ Υ ξ)
      rw [hpay]; exact hΥ _
  · rw [if_neg (fun h => hV h.2), if_pos hH]
    exact ⟨hC, by simp [payOf, fixW, fixE, hH, hV]⟩
  · rw [if_neg (fun h => hH h.1), if_neg hH, if_pos hV]
    exact ⟨hC, by simp [payOf, fixS, fixN, hH, hV]⟩
  · rw [if_neg (fun h => hH h.1), if_neg hH, if_neg hV]
    exact hC

end Tiles

/-- **`prop:tiles`.** If `M` does not halt, then `R_M` tiles. -/
theorem tiles_of_not_halts (M : TuringMachine) (hM : ¬ M.Halts) : Tiles (familyR M).toFinset := by
  obtain ⟨f, hf⟩ := exists_tower (diag third)
  obtain ⟨hq, hR, hL⟩ := positive_a hf
  obtain ⟨Υ, hΥ, hΥE, hΥN, hΥ0⟩ := horn_b M hM
  set ϑ := routedTiling hf
  let T : Plane → FTile := fun ξ => ⟨ϑ ξ, payOf ϑ Υ ξ⟩
  refine ⟨fun ξ => (T ξ).toTile, fun ξ => ?_, fun ξ => ?_, fun ξ => ?_⟩
  · exact List.mem_toFinset.2 (toTile_mem_familyR ⟨hR ξ, payOf_palette hf hq hR hL hΥ hΥ0 ξ⟩)
  · obtain ⟨hmq, hmf⟩ := hL.1 ξ trivial trivial
    refine FTile.toTile_E_W hmq hmf ?_
    show (payOf ϑ Υ ξ).E = (payOf ϑ Υ (ξ + (1, 0))).W
    simp only [payOf, add_sub_cancel_right]
    by_cases h1 : (ϑ ξ).HCarrier <;> by_cases h2 : (ϑ (ξ + (1, 0))).HCarrier
    · rw [if_pos h1, if_pos h2]; exact fixE_eq_fixW hf hq hR hL hΥE h1 h2
    · rw [if_pos h1, if_neg h2, if_pos h1]
    · rw [if_neg h1, if_pos h2, if_pos h2]
    · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
  · obtain ⟨hmq, hmf⟩ := hL.2 ξ trivial trivial
    refine FTile.toTile_N_S hmq hmf ?_
    show (payOf ϑ Υ ξ).N = (payOf ϑ Υ (ξ + (0, 1))).S
    simp only [payOf, add_sub_cancel_right]
    by_cases h1 : (ϑ ξ).VCarrier <;> by_cases h2 : (ϑ (ξ + (0, 1))).VCarrier
    · rw [if_pos h1, if_pos h2]; exact fixN_eq_fixS hf hq hR hL hΥN h1 h2
    · rw [if_pos h1, if_neg h2, if_pos h1]
    · rw [if_neg h1, if_pos h2, if_pos h2]
    · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]

end FNE.Family
