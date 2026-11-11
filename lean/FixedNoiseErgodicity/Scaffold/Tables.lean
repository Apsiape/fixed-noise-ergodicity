/-
# Section 5 and Appendix A: the tables of the scaffold

Transcribed from Appendix A of the paper (`appendix-tables.tex`, v1.3.0) and `scf:def-ruler`;
the paper says (05:17) that its proofs use only these tables, so they are the source here.
Cross-checks: lean-wang's 104 triples (`Closed104/Data.lean`, read on the web, not vendored)
equal `𝕆` exactly (one-off comparison, session 4; `BLUEPRINT.md`, Part C), and the kernel
reproduces the corner-lemma programs' count of 4496 compatible directional pairs
(`fit_pairs_count` in `Scaffold/WangSet.lean`).

* `scf:tab-edges`: the thin types `a, b, c, d`, the thick types (four corners `∠a, …, ∠d`, sixteen
  lines `⟨α, γ⟩`), the black types `A, …, E`, and their endpoints on the four sides.
  **[choice]** Endpoints are typed: north and south endpoints are vertical atoms
  `r₀, r₂, g₀, g₂` (`VAtom`), east and west endpoints are horizontal atoms `r₁, r₃, g₁, g₃`
  (`HAtom`). Every entry of the printed table respects this split, and it is what makes the line
  `⟨α, γ⟩` a typed constructor. Black bits are `Bool` (`false` is `0`).
* The maps `F`, `se`, `nw` (App. A, lines 34–46) and their listed properties.
* `scf:tab-alphabet`: the base set `𝕆` (`Formal.InO`), row by row; 104 triples.
* `scf:def-ruler`: the letters of the scaffold `𝔸` (`Letter.InA`, conditions (R1)–(R4)); 276.
* `scf:tab-letters`: the eight rows of the count, and `scf:tab-parents` (128 formal parents).

Kernel cost (measured, session 4): every finite check is `decide +kernel` (no `native_decide`)
on a *linear* computation over explicit enumeration lists (400 formal triples, 1600 formal
letters): the counts below take a few seconds and little memory. Two forms are avoided because the
kernel needs more than 3–4 GB for them: `Nodup` of a long list (quadratic; proved structurally
here, `nodup_flatMap_of_key`), and a bounded quantifier `∀ x ∈ l, P x` decided through its
`Decidable` instance (it builds proof terms at every step); such checks are written as Boolean
folds `l.all p = true`.

**Format for the corner-lemma certificate (Part E).** The 276 letters are the list `letters`, in
the order of `Letter.all` (thin, thick, black, `b₁`, `b₂`, each in the order of its `all` list),
so a letter is a `Fin 276` index into `letters`. The certificate will use exactly these tables:
`letters`, the colours `Letter.colN/E/S/W` (with natural-number codes in `Scaffold/WangSet.lean`),
and the matching relations `Letter.MatchE`, `Letter.MatchN`.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Nodup

set_option autoImplicit false

-- The kernel checks below walk lists of up to 1600 entries; the elaborator's recursion counter
-- must allow that depth (this changes no proof obligation).
set_option maxRecDepth 20000

namespace FNE.Scaffold

/-- A `flatMap` of a duplicate-free list is duplicate-free if each block is, and every entry of
the block of `a` remembers `a`. Used instead of a kernel `Nodup` check, which is quadratic. -/
theorem nodup_flatMap_of_key {α β : Type*} {l : List α} {f : α → List β} (key : β → α)
    (hl : l.Nodup) (hf : ∀ a ∈ l, (f a).Nodup) (hkey : ∀ a, ∀ b ∈ f a, key b = a) :
    (l.flatMap f).Nodup :=
  List.nodup_flatMap.2 ⟨hf, hl.imp fun {a a'} hne b hb hb' =>
    hne ((hkey a b hb).symm.trans (hkey a' b hb'))⟩

/-! ## Atoms (App. A, opening paragraph) -/

/-- App. A: the vertical lane atoms `r₀, r₂, g₀, g₂` (`r` red, `g` green). -/
inductive VAtom where
  | r0 | r2 | g0 | g2
  deriving DecidableEq, Repr

/-- App. A: the horizontal lane atoms `r₁, r₃, g₁, g₃`. -/
inductive HAtom where
  | r1 | r3 | g1 | g3
  deriving DecidableEq, Repr

namespace VAtom

/-- All vertical atoms, in a fixed order. -/
def all : List VAtom := [r0, r2, g0, g2]

theorem mem_all (x : VAtom) : x ∈ all := by cases x <;> decide

theorem all_nodup : all.Nodup := by decide

instance : Fintype VAtom := ⟨⟨all, all_nodup⟩, fun x => Multiset.mem_coe.2 (mem_all x)⟩

/-- The atoms `r₀, r₂` are red. -/
def IsRed : VAtom → Prop
  | r0 => True
  | r2 => True
  | g0 => False
  | g2 => False

instance : DecidablePred IsRed := fun x => by cases x <;> unfold IsRed <;> infer_instance

end VAtom

namespace HAtom

/-- All horizontal atoms, in a fixed order. -/
def all : List HAtom := [r1, r3, g1, g3]

theorem mem_all (x : HAtom) : x ∈ all := by cases x <;> decide

theorem all_nodup : all.Nodup := by decide

instance : Fintype HAtom := ⟨⟨all, all_nodup⟩, fun x => Multiset.mem_coe.2 (mem_all x)⟩

/-- The atoms `r₁, r₃` are red. -/
def IsRed : HAtom → Prop
  | r1 => True
  | r3 => True
  | g1 => False
  | g3 => False

instance : DecidablePred IsRed := fun x => by cases x <;> unfold IsRed <;> infer_instance

end HAtom

/-! ## The three components and their endpoints (`scf:tab-edges`) -/

/-- §5.1: the thin types `a, b, c, d`. -/
inductive Thin where
  | a | b | c | d
  deriving DecidableEq, Repr

/-- §5.1: the four corners `∠a, ∠b, ∠c, ∠d`. -/
inductive Corner where
  | a | b | c | d
  deriving DecidableEq, Repr

/-- §5.1: a thick type is a corner or a line `⟨α, γ⟩` with a vertical atom `α` and a horizontal
atom `γ`. -/
inductive Thick where
  | corner (k : Corner)
  | line (α : VAtom) (γ : HAtom)
  deriving DecidableEq, Repr

/-- §5.1: the black types `A, B, C, D, E`. -/
inductive Black where
  | A | B | C | D | E
  deriving DecidableEq, Repr

namespace Thin

/-- All thin types, in a fixed order. -/
def all : List Thin := [a, b, c, d]

theorem mem_all (x : Thin) : x ∈ all := by cases x <;> decide

theorem all_nodup : all.Nodup := by decide

instance : Fintype Thin := ⟨⟨all, all_nodup⟩, fun x => Multiset.mem_coe.2 (mem_all x)⟩

/-- `scf:tab-edges`: north endpoints of the thin types. -/
def epN : Thin → VAtom
  | a => .r0 | b => .g0 | c => .r2 | d => .g2

/-- `scf:tab-edges`: south endpoints of the thin types. -/
def epS : Thin → VAtom
  | a => .g2 | b => .r2 | c => .g0 | d => .r0

/-- `scf:tab-edges`: east endpoints of the thin types. -/
def epE : Thin → HAtom
  | a => .r1 | b => .g1 | c => .g3 | d => .r3

/-- `scf:tab-edges`: west endpoints of the thin types. -/
def epW : Thin → HAtom
  | a => .g3 | b => .r3 | c => .r1 | d => .g1

end Thin

namespace Corner

/-- All corners, in a fixed order. -/
def all : List Corner := [a, b, c, d]

theorem mem_all (x : Corner) : x ∈ all := by cases x <;> decide

theorem all_nodup : all.Nodup := by decide

instance : Fintype Corner := ⟨⟨all, all_nodup⟩, fun x => Multiset.mem_coe.2 (mem_all x)⟩

/-- `scf:tab-edges`: north endpoints of the corners. -/
def epN : Corner → VAtom
  | a => .g2 | b => .r0 | c => .r2 | d => .g0

/-- `scf:tab-edges`: south endpoints of the corners. -/
def epS : Corner → VAtom
  | a => .r0 | b => .g2 | c => .g0 | d => .r2

/-- `scf:tab-edges`: east endpoints of the corners. -/
def epE : Corner → HAtom
  | a => .r3 | b => .r1 | c => .g3 | d => .g1

/-- `scf:tab-edges`: west endpoints of the corners. -/
def epW : Corner → HAtom
  | a => .g1 | b => .g3 | c => .r1 | d => .r3

end Corner

namespace Thick

/-- All thick types: the four corners, then the sixteen lines. -/
def all : List Thick :=
  Corner.all.map corner ++ VAtom.all.flatMap fun α => HAtom.all.map (line α)

theorem mem_all (x : Thick) : x ∈ all := by
  cases x with
  | corner k => exact List.mem_append_left _ (List.mem_map_of_mem (Corner.mem_all k))
  | line α γ =>
    exact List.mem_append_right _
      (List.mem_flatMap.2 ⟨α, VAtom.mem_all α, List.mem_map_of_mem (HAtom.mem_all γ)⟩)

theorem all_nodup : all.Nodup := by decide

instance : Fintype Thick := ⟨⟨all, all_nodup⟩, fun x => Multiset.mem_coe.2 (mem_all x)⟩

/-- `scf:tab-edges`: north endpoint; a line `⟨α, γ⟩` has `α`. -/
def epN : Thick → VAtom
  | corner k => k.epN
  | line α _ => α

/-- `scf:tab-edges`: south endpoint; a line `⟨α, γ⟩` has `α`. -/
def epS : Thick → VAtom
  | corner k => k.epS
  | line α _ => α

/-- `scf:tab-edges`: east endpoint; a line `⟨α, γ⟩` has `γ`. -/
def epE : Thick → HAtom
  | corner k => k.epE
  | line _ γ => γ

/-- `scf:tab-edges`: west endpoint; a line `⟨α, γ⟩` has `γ`. -/
def epW : Thick → HAtom
  | corner k => k.epW
  | line _ γ => γ

/-- The thick type is a corner. -/
def IsCorner : Thick → Prop
  | corner _ => True
  | line _ _ => False

instance : DecidablePred IsCorner := fun x => by cases x <;> unfold IsCorner <;> infer_instance

/-- §5.2: a *red crossing* is a line whose two atoms are red. -/
def IsRedCrossing : Thick → Prop
  | corner _ => False
  | line α γ => α.IsRed ∧ γ.IsRed

instance : DecidablePred IsRedCrossing := fun x => by
  cases x <;> unfold IsRedCrossing <;> infer_instance

end Thick

namespace Black

/-- All black types, in a fixed order. -/
def all : List Black := [A, B, C, D, E]

theorem mem_all (x : Black) : x ∈ all := by cases x <;> decide

theorem all_nodup : all.Nodup := by decide

instance : Fintype Black := ⟨⟨all, all_nodup⟩, fun x => Multiset.mem_coe.2 (mem_all x)⟩

/-- `scf:tab-edges`: north bits of the black types (`true` is `1`). -/
def bitN : Black → Bool
  | A => false | B => true | C => true | D => true | E => false

/-- `scf:tab-edges`: south bits of the black types. -/
def bitS : Black → Bool
  | A => true | B => false | C => false | D => true | E => false

/-- `scf:tab-edges`: east bits of the black types. -/
def bitE : Black → Bool
  | A => false | B => false | C => true | D => true | E => true

/-- `scf:tab-edges`: west bits of the black types. -/
def bitW : Black → Bool
  | A => true | B => false | C => true | D => false | E => false

end Black

/-! ## The maps `F`, `se`, `nw` (App. A, lines 34–46) -/

/-- App. A, line 34: `F(a) = ∠b`, `F(b) = ∠d`, `F(c) = ∠c`, `F(d) = ∠a`; the corner with the four
endpoints of a thin type. -/
def F : Thin → Corner
  | .a => .b | .b => .d | .c => .c | .d => .a

/-- App. A, the black map `se`. -/
def se : Black → Black
  | .A => .B | .B => .B | .C => .C | .D => .C | .E => .C

/-- App. A, the black map `nw`. -/
def nw : Black → Black
  | .A => .E | .B => .D | .C => .D | .D => .D | .E => .E

/-- App. A, line 34: each corner `F(θ)` has exactly the four endpoints of `θ`. -/
theorem F_epN (θ : Thin) : (F θ).epN = θ.epN := by cases θ <;> rfl
theorem F_epS (θ : Thin) : (F θ).epS = θ.epS := by cases θ <;> rfl
theorem F_epE (θ : Thin) : (F θ).epE = θ.epE := by cases θ <;> rfl
theorem F_epW (θ : Thin) : (F θ).epW = θ.epW := by cases θ <;> rfl

/-- `F` is a bijection from thin types to corners (used in `scf:base`(c)). -/
theorem F_injective : Function.Injective F := by decide

theorem F_surjective : Function.Surjective F := by decide

/-- App. A, line 35: thin types match horizontally (west tile first) exactly in the pairs
`(a,c), (c,a), (b,d), (d,b)`. -/
theorem thin_matchE_iff (θ θ' : Thin) :
    θ.epE = θ'.epW ↔ (θ, θ') ∈ [(.a, .c), (.c, .a), (.b, .d), (.d, .b)] := by
  cases θ <;> cases θ' <;> decide

/-- App. A, line 35: thin types match vertically (south tile first) exactly in the pairs
`(a,d), (d,a), (b,c), (c,b)`. -/
theorem thin_matchN_iff (θ θ' : Thin) :
    θ.epN = θ'.epS ↔ (θ, θ') ∈ [(.a, .d), (.d, .a), (.b, .c), (.c, .b)] := by
  cases θ <;> cases θ' <;> decide

/-- App. A, line 46: `se(ω) ∈ {B, C}` is characterized by `∂_W se(ω) = ∂_E ω`. -/
theorem se_spec (ω : Black) : (se ω = .B ∨ se ω = .C) ∧ (se ω).bitW = ω.bitE := by
  cases ω <;> decide

theorem se_unique (ω ω' : Black) (h : ω' = .B ∨ ω' = .C) (h' : ω'.bitW = ω.bitE) :
    ω' = se ω := by
  rcases h with rfl | rfl <;> cases ω <;> simp_all [Black.bitW, Black.bitE, se]

/-- App. A, line 46: `nw(ω) ∈ {D, E}` is characterized by `∂_S nw(ω) = ∂_N ω`. -/
theorem nw_spec (ω : Black) : (nw ω = .D ∨ nw ω = .E) ∧ (nw ω).bitS = ω.bitN := by
  cases ω <;> decide

theorem nw_unique (ω ω' : Black) (h : ω' = .D ∨ ω' = .E) (h' : ω'.bitS = ω.bitN) :
    ω' = nw ω := by
  rcases h with rfl | rfl <;> cases ω <;> simp_all [Black.bitS, Black.bitN, nw]

/-- App. A, line 46: the six further identities of `se` and `nw`. -/
theorem se_bitE (ω : Black) : (se ω).bitE = ω.bitE := by cases ω <;> rfl
theorem nw_bitN (ω : Black) : (nw ω).bitN = ω.bitN := by cases ω <;> rfl
theorem se_bitS (ω : Black) : (se ω).bitS = false := by cases ω <;> rfl
theorem nw_bitW (ω : Black) : (nw ω).bitW = false := by cases ω <;> rfl
theorem se_bitN (ω : Black) : (se ω).bitN = true := by cases ω <;> rfl
theorem nw_bitE (ω : Black) : (nw ω).bitE = true := by cases ω <;> rfl

/-! ## Formal triples and the base set `𝕆` (`scf:def-base`, `scf:tab-alphabet`) -/

/-- §5.1: a *formal triple* `(θ, κ, ω)` of a thin, a thick and a black type. -/
structure Formal where
  /-- the thin type `θ` -/
  thin : Thin
  /-- the thick type `κ` -/
  thick : Thick
  /-- the black type `ω` -/
  black : Black
  deriving DecidableEq, Repr

namespace Formal

/-- All 400 formal triples, in a fixed order (thin, then thick, then black). -/
def all : List Formal :=
  Thin.all.flatMap fun θ => Thick.all.flatMap fun κ => Black.all.map fun ω => ⟨θ, κ, ω⟩

theorem mem_all (t : Formal) : t ∈ all := by
  obtain ⟨θ, κ, ω⟩ := t
  exact List.mem_flatMap.2 ⟨θ, Thin.mem_all θ, List.mem_flatMap.2
    ⟨κ, Thick.mem_all κ, List.mem_map_of_mem (Black.mem_all ω)⟩⟩

/-- Proved structurally (each block remembers its key), not by `decide`: a kernel check of
`Nodup` on 400 entries makes 80000 comparisons and needs more than 3 GB. -/
theorem all_nodup : all.Nodup :=
  nodup_flatMap_of_key thin Thin.all_nodup
    (fun θ _ => nodup_flatMap_of_key thick Thick.all_nodup
      (fun κ _ => Black.all_nodup.map fun _ _ h => by cases h; rfl)
      (fun κ t ht => by obtain ⟨ω, -, rfl⟩ := List.mem_map.1 ht; rfl))
    (fun θ t ht => by
      obtain ⟨κ, -, ht⟩ := List.mem_flatMap.1 ht
      obtain ⟨ω, -, rfl⟩ := List.mem_map.1 ht; rfl)

instance : Fintype Formal := ⟨⟨all, all_nodup⟩, fun x => Multiset.mem_coe.2 (mem_all x)⟩

theorem all_length : all.length = 400 := by decide +kernel

/-- `scf:tab-alphabet`, row by row: the base set `𝕆`. A row `θ, line, ω, condition` admits the
lines `⟨α, γ⟩` that satisfy the condition; a row `θ, corner, A` admits the four corners. -/
def inO : Formal → Bool
  | ⟨.a, .corner _, .A⟩ => true
  | ⟨.a, .line α _, .B⟩ => α != .r0
  | ⟨.a, .line α _, .C⟩ => α != .r2
  | ⟨.a, .line _ γ, .D⟩ => γ != .r3
  | ⟨.a, .line _ γ, .E⟩ => γ != .r1
  | ⟨.b, .corner _, .A⟩ => true
  | ⟨.c, .line α _, .B⟩ => α != .r0
  | ⟨.c, .line α _, .C⟩ => α != .r2
  | ⟨.d, .line _ γ, .D⟩ => γ != .r3
  | ⟨.d, .line _ γ, .E⟩ => γ != .r1
  | _ => false

/-- `scf:def-base`: the triple `t` is a tile of `𝕆`. -/
def InO (t : Formal) : Prop := t.inO = true

instance : DecidablePred InO := fun t => inferInstanceAs (Decidable (t.inO = true))

/-- The 104 triples of `𝕆`, in the order of `Formal.all`. -/
def baseList : List Formal := all.filter inO

theorem mem_baseList {t : Formal} : t ∈ baseList ↔ t.InO := by
  simp [baseList, InO, mem_all]

theorem baseList_nodup : baseList.Nodup := all_nodup.filter _

/-- `scf:def-base`, `scf:tab-alphabet`: `𝕆` has 104 triples. -/
theorem baseList_length : baseList.length = 104 := by decide +kernel

/-- `scf:tab-alphabet`: the ten rows, counted. -/
theorem tab_alphabet_rows :
    (baseList.filter fun t => t.thin = .a ∧ t.thick.IsCorner ∧ t.black = .A).length = 4 ∧
    (baseList.filter fun t => t.thin = .a ∧ ¬ t.thick.IsCorner ∧ t.black = .B).length = 12 ∧
    (baseList.filter fun t => t.thin = .a ∧ ¬ t.thick.IsCorner ∧ t.black = .C).length = 12 ∧
    (baseList.filter fun t => t.thin = .a ∧ ¬ t.thick.IsCorner ∧ t.black = .D).length = 12 ∧
    (baseList.filter fun t => t.thin = .a ∧ ¬ t.thick.IsCorner ∧ t.black = .E).length = 12 ∧
    (baseList.filter fun t => t.thin = .b ∧ t.thick.IsCorner ∧ t.black = .A).length = 4 ∧
    (baseList.filter fun t => t.thin = .c ∧ ¬ t.thick.IsCorner ∧ t.black = .B).length = 12 ∧
    (baseList.filter fun t => t.thin = .c ∧ ¬ t.thick.IsCorner ∧ t.black = .C).length = 12 ∧
    (baseList.filter fun t => t.thin = .d ∧ ¬ t.thick.IsCorner ∧ t.black = .D).length = 12 ∧
    (baseList.filter fun t => t.thin = .d ∧ ¬ t.thick.IsCorner ∧ t.black = .E).length = 12 := by
  decide

/-- `scf:tab-alphabet`: every corner of `𝕆` has black type `A`, with thin type `a` or `b`. -/
theorem InO.corner {t : Formal} (h : t.InO) (hc : t.thick.IsCorner) :
    t.black = .A ∧ (t.thin = .a ∨ t.thin = .b) := by
  obtain ⟨θ, κ, ω⟩ := t
  cases κ with
  | line _ _ => exact hc.elim
  | corner k => cases θ <;> cases ω <;> cases k <;> simp_all [InO, inO]

/-! ### Colours of formal triples -/

/-- `scf:def-base`: the colour of `(θ, κ, ω)` on the north side, `(∂_N θ, ∂_N κ, ∂_N ω)`. -/
def colN (t : Formal) : VAtom × VAtom × Bool := (t.thin.epN, t.thick.epN, t.black.bitN)

/-- `scf:def-base`: the colour on the south side. -/
def colS (t : Formal) : VAtom × VAtom × Bool := (t.thin.epS, t.thick.epS, t.black.bitS)

/-- `scf:def-base`: the colour on the east side. -/
def colE (t : Formal) : HAtom × HAtom × Bool := (t.thin.epE, t.thick.epE, t.black.bitE)

/-- `scf:def-base`: the colour on the west side. -/
def colW (t : Formal) : HAtom × HAtom × Bool := (t.thin.epW, t.thick.epW, t.black.bitW)

/-- §5 (opening): `t, t'` match in direction `e₁` if `t_E = t'_W`. -/
def MatchE (t t' : Formal) : Prop := t.colE = t'.colW

/-- §5 (opening): `t, t'` match in direction `e₂` if `t_N = t'_S`. -/
def MatchN (t t' : Formal) : Prop := t.colN = t'.colS

instance : DecidableRel MatchE := fun t t' => inferInstanceAs (Decidable (t.colE = t'.colW))

instance : DecidableRel MatchN := fun t t' => inferInstanceAs (Decidable (t.colN = t'.colS))

theorem matchE_iff {t t' : Formal} : MatchE t t' ↔
    t.thin.epE = t'.thin.epW ∧ t.thick.epE = t'.thick.epW ∧ t.black.bitE = t'.black.bitW := by
  simp [MatchE, colE, colW]

theorem matchN_iff {t t' : Formal} : MatchN t t' ↔
    t.thin.epN = t'.thin.epS ∧ t.thick.epN = t'.thick.epS ∧ t.black.bitN = t'.black.bitS := by
  simp [MatchN, colN, colS]

/-- §5.1 (after `scf:def-base`): distinct triples have distinct colours, so the 104 triples of `𝕆`
give 104 distinct tiles. This holds for all 400 formal triples. -/
theorem col_injective {t t' : Formal} (hN : t.colN = t'.colN) (hS : t.colS = t'.colS)
    (hE : t.colE = t'.colE) (hW : t.colW = t'.colW) : t = t' := by
  obtain ⟨θ, κ, ω⟩ := t
  obtain ⟨θ', κ', ω'⟩ := t'
  simp only [colN, colS, colE, colW, Prod.mk.injEq] at hN hS hE hW
  obtain ⟨h1, h2, h3⟩ := hN
  obtain ⟨-, h5, h6⟩ := hS
  obtain ⟨-, h8, h9⟩ := hE
  obtain ⟨-, -, h12⟩ := hW
  have hθ : θ = θ' := by cases θ <;> cases θ' <;> simp_all [Thin.epN]
  have hω : ω = ω' := by
    cases ω <;> cases ω' <;> simp_all [Black.bitN, Black.bitS, Black.bitE, Black.bitW]
  have hκ : κ = κ' := by
    cases κ with
    | corner k =>
      cases κ' with
      | corner k' => cases k <;> cases k' <;> simp_all [Thick.epN, Thick.epS, Corner.epN, Corner.epS]
      | line α γ => cases k <;> cases α <;> simp_all [Thick.epN, Thick.epS, Corner.epN, Corner.epS]
    | line α γ =>
      cases κ' with
      | corner k' => cases k' <;> cases α <;> simp_all [Thick.epN, Thick.epS, Corner.epN, Corner.epS]
      | line α' γ' => simp_all [Thick.epN, Thick.epE]
  subst hθ hω hκ; rfl

end Formal

/-! ## The letters of the scaffold `𝔸` (`scf:def-ruler`, `scf:tab-letters`) -/

/-- `scf:def-ruler`: a formal letter `(θ, κ, ω, b₁, b₂)`: a formal triple and two bits.
**[choice]** Bits are `Bool` (`false` is `0`). -/
structure Letter where
  /-- the base `𝔞̄ = (θ, κ, ω)` -/
  base : Formal
  /-- the column bit `b₁ = χ₁(𝔞)` -/
  b1 : Bool
  /-- the row bit `b₂ = χ₂(𝔞)` -/
  b2 : Bool
  deriving DecidableEq, Repr

namespace Letter

/-- (R1): if `θ ∈ {b, c}` then `b₁ = 0`. -/
def R1 (x : Letter) : Prop := (x.base.thin = .b ∨ x.base.thin = .c) → x.b1 = false

/-- (R2): if `θ ∈ {b, d}` then `b₂ = 0`. -/
def R2 (x : Letter) : Prop := (x.base.thin = .b ∨ x.base.thin = .d) → x.b2 = false

/-- (R3): if `κ` is a corner then `b₁ = b₂`. -/
def R3 (x : Letter) : Prop := x.base.thick.IsCorner → x.b1 = x.b2

/-- (R4): if `κ` is a red crossing then `b₁ ≠ b₂`. -/
def R4 (x : Letter) : Prop := x.base.thick.IsRedCrossing → x.b1 ≠ x.b2

/-- `scf:def-ruler`: the scaffold `𝔸`: tuples with `(θ, κ, ω) ∈ 𝕆` satisfying (R1)–(R4). -/
def InA (x : Letter) : Prop := x.base.InO ∧ x.R1 ∧ x.R2 ∧ x.R3 ∧ x.R4

instance : DecidablePred InA := fun x => by
  unfold InA R1 R2 R3 R4; infer_instance

/-- All 1600 formal letters, in a fixed order (base in the order of `Formal.all`, then `b₁`, then
`b₂`, with `false` first). -/
def all : List Letter :=
  Formal.all.flatMap fun t => [false, true].flatMap fun b1 => [false, true].map fun b2 =>
    ⟨t, b1, b2⟩

theorem mem_all (x : Letter) : x ∈ all := by
  obtain ⟨t, b1, b2⟩ := x
  exact List.mem_flatMap.2 ⟨t, Formal.mem_all t, List.mem_flatMap.2
    ⟨b1, by cases b1 <;> simp, List.mem_map_of_mem (by cases b2 <;> simp)⟩⟩

/-- Proved structurally, as for `Formal.all_nodup`. -/
theorem all_nodup : all.Nodup :=
  nodup_flatMap_of_key base Formal.all_nodup
    (fun t _ => nodup_flatMap_of_key b1 (by decide)
      (fun b1 _ => (by decide : [false, true].Nodup).map fun _ _ h => by cases h; rfl)
      (fun b1 x hx => by obtain ⟨b2, -, rfl⟩ := List.mem_map.1 hx; rfl))
    (fun t x hx => by
      obtain ⟨b1, -, hx⟩ := List.mem_flatMap.1 hx
      obtain ⟨b2, -, rfl⟩ := List.mem_map.1 hx; rfl)

instance : Fintype Letter := ⟨⟨all, all_nodup⟩, fun x => Multiset.mem_coe.2 (mem_all x)⟩

/-- **The 276 letters of `𝔸`**, in the order of `Letter.all`. This list is the letter table used
by everything downstream; the corner-lemma certificate indexes letters by `Fin 276` into it. -/
def letters : List Letter := all.filter fun x => decide x.InA

theorem mem_letters {x : Letter} : x ∈ letters ↔ x.InA := by
  simp [letters, mem_all]

theorem letters_nodup : letters.Nodup := all_nodup.filter _

/-- `prop:scaffold`, `scf:tab-letters`: `𝔸` has 276 letters. -/
theorem letters_length : letters.length = 276 := by decide +kernel

/-- `scf:tab-letters`: the eight rows, counted (`184 + 4 + 44 + 44 = 276`). -/
theorem tab_letters_rows :
    (letters.filter fun x => x.base.thin = .a ∧ x.base.thick.IsCorner).length = 8 ∧
    (letters.filter fun x => x.base.thin = .a ∧ x.base.thick.IsRedCrossing).length = 16 ∧
    (letters.filter fun x => x.base.thin = .a ∧ ¬ x.base.thick.IsCorner ∧
      ¬ x.base.thick.IsRedCrossing).length = 160 ∧
    (letters.filter fun x => x.base.thin = .b).length = 4 ∧
    (letters.filter fun x => x.base.thin = .c ∧ x.base.thick.IsRedCrossing).length = 4 ∧
    (letters.filter fun x => x.base.thin = .c ∧ ¬ x.base.thick.IsRedCrossing).length = 40 ∧
    (letters.filter fun x => x.base.thin = .d ∧ x.base.thick.IsRedCrossing).length = 4 ∧
    (letters.filter fun x => x.base.thin = .d ∧ ¬ x.base.thick.IsRedCrossing).length = 40 := by
  decide +kernel

/-! ### Colours and matching of letters -/

/-- `scf:def-ruler`: the north colour is the north colour of the base together with `b₁`. -/
def colN (x : Letter) : (VAtom × VAtom × Bool) × Bool := (x.base.colN, x.b1)

/-- `scf:def-ruler`: the south colour is the south colour of the base together with `b₁`. -/
def colS (x : Letter) : (VAtom × VAtom × Bool) × Bool := (x.base.colS, x.b1)

/-- `scf:def-ruler`: the east colour is the east colour of the base together with `b₂`. -/
def colE (x : Letter) : (HAtom × HAtom × Bool) × Bool := (x.base.colE, x.b2)

/-- `scf:def-ruler`: the west colour is the west colour of the base together with `b₂`. -/
def colW (x : Letter) : (HAtom × HAtom × Bool) × Bool := (x.base.colW, x.b2)

/-- §5 (opening): letters `x, y` match in direction `e₁` if `x_E = y_W`. -/
def MatchE (x y : Letter) : Prop := x.colE = y.colW

/-- §5 (opening): letters `x, y` match in direction `e₂` if `x_N = y_S`. -/
def MatchN (x y : Letter) : Prop := x.colN = y.colS

instance : DecidableRel MatchE := fun x y => inferInstanceAs (Decidable (x.colE = y.colW))

instance : DecidableRel MatchN := fun x y => inferInstanceAs (Decidable (x.colN = y.colS))

theorem matchE_iff {x y : Letter} : MatchE x y ↔ x.base.MatchE y.base ∧ x.b2 = y.b2 := by
  simp [MatchE, colE, colW, Formal.MatchE]

theorem matchN_iff {x y : Letter} : MatchN x y ↔ x.base.MatchN y.base ∧ x.b1 = y.b1 := by
  simp [MatchN, colN, colS, Formal.MatchN]

/-- `prop:scaffold`(v), the *edgewise bit property*: letters that match in direction `e₂` have
equal column bits, and letters that match in direction `e₁` have equal row bits. It holds for
every matching pair. -/
theorem MatchN.b1_eq {x y : Letter} (h : MatchN x y) : x.b1 = y.b1 := (matchN_iff.1 h).2

theorem MatchE.b2_eq {x y : Letter} (h : MatchE x y) : x.b2 = y.b2 := (matchE_iff.1 h).2

/-- Distinct letters have distinct colours (so `𝔸` is a Wang set of 276 tiles). -/
theorem col_injective {x y : Letter} (hN : x.colN = y.colN) (hS : x.colS = y.colS)
    (hE : x.colE = y.colE) (hW : x.colW = y.colW) : x = y := by
  obtain ⟨t, b1, b2⟩ := x
  obtain ⟨t', b1', b2'⟩ := y
  simp only [colN, colS, colE, colW, Prod.mk.injEq] at hN hS hE hW
  rw [Formal.col_injective hN.1 hS.1 hE.1 hW.1, hN.2, hE.2]


end Letter

end FNE.Scaffold
