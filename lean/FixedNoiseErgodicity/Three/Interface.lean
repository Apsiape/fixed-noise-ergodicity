/-
# §7.1, (Q1)–(Q3) for the family `R_M` (07:23–27)

The tiles of `R_M` are the codes `FTile.toTile ϑ` of the candidates `ϑ` with `ϑ.InR M`
(`def:family`, `Family/FamilyR.lean`). The code is injective (`FTile.toTile_injective`: the
scaffold pair is read off the east and west colours, one of which is internal), so every tile of
`R_M` decodes to its candidate (`ofTile`), and the attributes of (Q1)–(Q3) are read off it:
* (Q1) the scaffold pair `(quad, par)` (`spair`, `tquad`, `tpar`); matching moves the quadrant by
  `e₁` (`e₂`) and keeps the parent or makes the parents match (`Q1_E`, `Q1_N`, from
  `fam:quarter`(a));
* (Q2) the walls are functions of the scaffold pair (`vWall`, `hWall` of `(tquad, tpar)`); flows
  (`flowW` … `flowN`) agree across matching edges (`Q2_E`, `Q2_N`) and obey the flow rules
  (`Q2_rulesH`, `Q2_rulesV`, from `fam:def-routed`);
* (Q3) carriers and roles (`IsHCarrier`, `IsVCarrier`, `trole`), payloads (`tpay`), equal across
  matching edges (`Q3_E`, `Q3_N`), in the palette of the role (`Q3_palette`, from `def:family`).
Also the class `quad(ϑ) − u (mod 2)` of a tile at a site (`cls`, 07:43) and its invariance under
matching (`cls_E`, `cls_N`), used by `thr:move` and `thr:phase`.

**[choice]** The attributes are defined on all tiles through the left inverse `ofTile` of the
code (`Function.invFun`); they are the printed ones on the tiles of `R_M` (`ofTile_spec`).
The class is a pair in `{0,1}²` (`Int.emod 2`).
-/
import FixedNoiseErgodicity.Family.FamilyR

set_option autoImplicit false

namespace FNE.Three

open FNE FNE.Scaffold FNE.Family

/-! ## The tiles of `R_M` and their decoding -/

/-- The Wang set `R_M` of `def:family`. -/
noncomputable abbrev RM (M : TuringMachine) : WangSet := (familyR M).toFinset

theorem mem_RM {M : TuringMachine} {t : Tile} :
    t ∈ RM M ↔ ∃ f : FTile, f.InR M ∧ f.toTile = t := by
  classical
  simp only [RM, List.mem_toFinset, familyR, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨f, ⟨-, hf⟩, rfl⟩; exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩; exact ⟨f, ⟨mem_ftileList hf, hf⟩, rfl⟩

/-- A scaffold pair is determined by its east and west colours (one of them is internal). -/
theorem SPair.eq_of_colE_colW {q q' : SPair} (hE : q.colE = q'.colE) (hW : q.colW = q'.colW) :
    q = q' := by
  obtain ⟨⟨s1, s2⟩, a⟩ := q
  obtain ⟨⟨t1, t2⟩, b⟩ := q'
  cases s1 <;> cases t1 <;> simp_all [SPair.colE, SPair.colW]

/-- The code of a candidate tile is injective. -/
theorem FTile.toTile_injective : Function.Injective FTile.toTile := by
  intro f f' h
  have hN := congrArg Tile.N h
  have hE := congrArg Tile.E h
  have hS := congrArg Tile.S h
  have hW := congrArg Tile.W h
  simp only [FTile.toTile, Nat.pair_eq_pair, Encodable.encode_inj, colCode_injective.eq_iff,
    Prod.mk.injEq] at hN hE hS hW
  obtain ⟨⟨q, fW, fE, fS, fN⟩, p⟩ := f
  obtain ⟨⟨q', fW', fE', fS', fN'⟩, p'⟩ := f'
  have hq : q = q' := SPair.eq_of_colE_colW hE.1.1 hW.1.1
  have hp : p = p' := Pay.ext hW.2 hE.2 hS.2 hN.2
  obtain ⟨⟨-, rfl⟩, -⟩ := hN
  obtain ⟨⟨-, rfl⟩, -⟩ := hE
  obtain ⟨⟨-, rfl⟩, -⟩ := hS
  obtain ⟨⟨-, rfl⟩, -⟩ := hW
  subst hq hp
  rfl

instance : Nonempty FTile :=
  ⟨⟨⟨⟨(false, false), index0Dark⟩, Flow.empty, Flow.empty, Flow.empty, Flow.empty⟩, ⟨∅, ∅, ∅, ∅⟩⟩⟩

/-- The decoding of a tile: the candidate whose code it is (a left inverse of the code). -/
noncomputable def ofTile : Tile → FTile := Function.invFun FTile.toTile

theorem ofTile_toTile (f : FTile) : ofTile f.toTile = f :=
  Function.leftInverse_invFun FTile.toTile_injective f

/-- A tile of `R_M` is the code of its decoding, which lies in `R_M`. -/
theorem ofTile_spec {M : TuringMachine} {t : Tile} (ht : t ∈ RM M) :
    (ofTile t).InR M ∧ (ofTile t).toTile = t := by
  obtain ⟨f, hf, rfl⟩ := mem_RM.1 ht
  rw [ofTile_toTile]
  exact ⟨hf, rfl⟩

/-! ## The attributes of (Q1)–(Q3) -/

/-- (Q1): the scaffold pair `(quad(ϑ), par(ϑ))` of a tile. -/
noncomputable def spair (t : Tile) : SPair := (ofTile t).r.q

/-- (Q1): the quadrant `quad(ϑ) ∈ {0,1}²`. -/
noncomputable def tquad (t : Tile) : Bool × Bool := (spair t).quad

/-- (Q1): the parent `par(ϑ) ∈ 𝔸`. -/
noncomputable def tpar (t : Tile) : Letter := (spair t).par

/-- (Q2): the west flow `φ_W(ϑ)`. -/
noncomputable def flowW (t : Tile) : Flow := (ofTile t).r.fW

/-- (Q2): the east flow `φ_E(ϑ)`. -/
noncomputable def flowE (t : Tile) : Flow := (ofTile t).r.fE

/-- (Q2): the south flow `φ_S(ϑ)`. -/
noncomputable def flowS (t : Tile) : Flow := (ofTile t).r.fS

/-- (Q2): the north flow `φ_N(ϑ)`. -/
noncomputable def flowN (t : Tile) : Flow := (ofTile t).r.fN

/-- (Q3): `ϑ` is a horizontal carrier: `φ_W(ϑ) = φ_E(ϑ) = ∅`. -/
def IsHCarrier (t : Tile) : Prop := flowW t = Flow.empty ∧ flowE t = Flow.empty

/-- (Q3): `ϑ` is a vertical carrier: `φ_S(ϑ) = φ_N(ϑ) = ∅`. -/
def IsVCarrier (t : Tile) : Prop := flowS t = Flow.empty ∧ flowN t = Flow.empty

/-- (Q3): the role of `ϑ` (06:160). -/
noncomputable def trole (t : Tile) : Role := (ofTile t).r.role

/-- (Q3): the payload `pay(ϑ) ∈ C_M^4`. -/
noncomputable def tpay (t : Tile) : Pay := (ofTile t).pay

noncomputable instance (t : Tile) : Decidable (IsHCarrier t) := inferInstanceAs (Decidable (_ ∧ _))

noncomputable instance (t : Tile) : Decidable (IsVCarrier t) := inferInstanceAs (Decidable (_ ∧ _))

theorem isHCarrier_iff (t : Tile) : IsHCarrier t ↔ (ofTile t).r.HCarrier := Iff.rfl

theorem isVCarrier_iff (t : Tile) : IsVCarrier t ↔ (ofTile t).r.VCarrier := Iff.rfl

/-- (Q3): the role is inactive, horizontal, vertical or active according to the carriers, and
seed in place of active on the north-east quarter of the index-`0` dark letter. -/
theorem trole_eq (t : Tile) :
    trole t = if IsHCarrier t ∧ IsVCarrier t then
      (if spair t = ⟨(true, true), index0Dark⟩ then Role.seed else Role.active)
      else if IsHCarrier t then Role.horiz else if IsVCarrier t then Role.vert
      else Role.inactive := rfl

variable {M : TuringMachine} {t t' : Tile}

/-- The parent of a tile of `R_M` is a letter of `𝔸`. -/
theorem tpar_inA (ht : t ∈ RM M) : (tpar t).InA := (ofTile_spec ht).1.1.1

/-- The code of the decodings of matching tiles. -/
theorem toTile_ofTile_E (ht : t ∈ RM M) (ht' : t' ∈ RM M) (h : t.E = t'.W) :
    (ofTile t).toTile.E = (ofTile t').toTile.W := by
  rw [(ofTile_spec ht).2, (ofTile_spec ht').2]; exact h

theorem toTile_ofTile_N (ht : t ∈ RM M) (ht' : t' ∈ RM M) (h : t.N = t'.S) :
    (ofTile t).toTile.N = (ofTile t').toTile.S := by
  rw [(ofTile_spec ht).2, (ofTile_spec ht').2]; exact h

/-- **(Q1)**, horizontally: if `ϑ, ϑ'` match horizontally, then `quad(ϑ') ≡ quad(ϑ) + e₁`, and
`par(ϑ') = par(ϑ)` if the first coordinate of `quad(ϑ)` is `0`, while `par(ϑ), par(ϑ')` match
horizontally in `𝔸` if it is `1`. -/
theorem Q1_E (ht : t ∈ RM M) (ht' : t' ∈ RM M) (h : t.E = t'.W) :
    (tquad t').1 = !(tquad t).1 ∧ (tquad t').2 = (tquad t).2 ∧
      ((tquad t).1 = false ∧ tpar t' = tpar t ∨
        (tquad t).1 = true ∧ Letter.MatchE (tpar t) (tpar t')) :=
  (SPair.matchE_iff _ _).1 ((FTile.toTile_E_W_iff _ _).1 (toTile_ofTile_E ht ht' h)).1

/-- **(Q1)**, vertically. -/
theorem Q1_N (ht : t ∈ RM M) (ht' : t' ∈ RM M) (h : t.N = t'.S) :
    (tquad t').2 = !(tquad t).2 ∧ (tquad t').1 = (tquad t).1 ∧
      ((tquad t).2 = false ∧ tpar t' = tpar t ∨
        (tquad t).2 = true ∧ Letter.MatchN (tpar t) (tpar t')) :=
  (SPair.matchN_iff _ _).1 ((FTile.toTile_N_S_iff _ _).1 (toTile_ofTile_N ht ht' h)).1

/-- **(Q2)**: flows agree across a horizontal edge. -/
theorem Q2_E (ht : t ∈ RM M) (ht' : t' ∈ RM M) (h : t.E = t'.W) : flowE t = flowW t' :=
  ((FTile.toTile_E_W_iff _ _).1 (toTile_ofTile_E ht ht' h)).2.1

/-- **(Q2)**: flows agree across a vertical edge. -/
theorem Q2_N (ht : t ∈ RM M) (ht' : t' ∈ RM M) (h : t.N = t'.S) : flowN t = flowS t' :=
  ((FTile.toTile_N_S_iff _ _).1 (toTile_ofTile_N ht ht' h)).2.1

/-- **(Q2)**: the horizontal flow rules, for the light vertical wall of the scaffold pair: no wall,
`φ_W = φ_E`; a left side (`lo`), `φ_W ≠ ∅` and `φ_E ⊆ {left}`; a right side (`hi`), `φ_E ≠ ∅` and
`φ_W ⊆ {right}`. -/
theorem Q2_rulesH (ht : t ∈ RM M) : FlowRules (vWall (tquad t) (tpar t)) (flowW t) (flowE t) :=
  (ofTile_spec ht).1.1.2.1

/-- **(Q2)**: the vertical flow rules, for the light horizontal wall of the scaffold pair. -/
theorem Q2_rulesV (ht : t ∈ RM M) : FlowRules (hWall (tquad t) (tpar t)) (flowS t) (flowN t) :=
  (ofTile_spec ht).1.1.2.2

/-- **(Q3)**: payloads agree across a horizontal edge. -/
theorem Q3_E (ht : t ∈ RM M) (ht' : t' ∈ RM M) (h : t.E = t'.W) : (tpay t).E = (tpay t').W :=
  ((FTile.toTile_E_W_iff _ _).1 (toTile_ofTile_E ht ht' h)).2.2

/-- **(Q3)**: payloads agree across a vertical edge. -/
theorem Q3_N (ht : t ∈ RM M) (ht' : t' ∈ RM M) (h : t.N = t'.S) : (tpay t).N = (tpay t').S :=
  ((FTile.toTile_N_S_iff _ _).1 (toTile_ofTile_N ht ht' h)).2.2

/-- **(Q3)**: the payload lies in the palette of the role. -/
theorem Q3_palette (ht : t ∈ RM M) : palette M (trole t) (tpay t) := (ofTile_spec ht).1.2

/-! ## The class `quad(ϑ) − u (mod 2)` -/

/-- The class of `quad(ϑ) − u` modulo `2`, as a pair in `{0,1}²` (07:43). -/
noncomputable def cls (u : Plane) (t : Tile) : Plane :=
  ((bitZ (tquad t).1 - u.1) % 2, (bitZ (tquad t).2 - u.2) % 2)

theorem bitZ_not (b : Bool) : bitZ (!b) = 1 - bitZ b := by cases b <;> rfl

/-- Horizontally matching tiles at `u` and `u + e₁` have the same class. -/
theorem cls_E (ht : t ∈ RM M) (ht' : t' ∈ RM M) (h : t.E = t'.W) (u : Plane) :
    cls (u + (1, 0)) t' = cls u t := by
  obtain ⟨h1, h2, -⟩ := Q1_E ht ht' h
  simp only [cls, h1, h2, bitZ_not, Prod.fst_add, Prod.snd_add, add_zero, Prod.mk.injEq, and_true]
  omega

/-- Vertically matching tiles at `u` and `u + e₂` have the same class. -/
theorem cls_N (ht : t ∈ RM M) (ht' : t' ∈ RM M) (h : t.N = t'.S) (u : Plane) :
    cls (u + (0, 1)) t' = cls u t := by
  obtain ⟨h1, h2, -⟩ := Q1_N ht ht' h
  simp only [cls, h1, h2, bitZ_not, Prod.fst_add, Prod.snd_add, add_zero, Prod.mk.injEq, true_and]
  omega

/-- The class determines the quadrant: `quad(ϑ) ≡ x − γ (mod 2)` if `cls x ϑ = γ`. -/
theorem quad_of_cls {x γ : Plane} (h : cls x t = γ) :
    bitZ (tquad t).1 = (x.1 - γ.1) % 2 ∧ bitZ (tquad t).2 = (x.2 - γ.2) % 2 := by
  rw [← h]
  simp only [cls]
  have h1 := bitZ_nonneg (tquad t).1
  have h2 := bitZ_le_one (tquad t).1
  have h3 := bitZ_nonneg (tquad t).2
  have h4 := bitZ_le_one (tquad t).2
  constructor <;> omega

theorem eq_false_of_bitZ {b : Bool} (h : bitZ b = 0) : b = false := by
  cases b <;> simp_all [bitZ]

theorem eq_true_of_bitZ {b : Bool} (h : bitZ b = 1) : b = true := by
  cases b <;> simp_all [bitZ]

end FNE.Three
