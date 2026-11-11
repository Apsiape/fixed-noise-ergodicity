/-
# Section 5: the scaffold `𝔸` as a Wang set of tiles (`prop:scaffold`)

* Colour codes: each colour of a letter is coded by a natural number (`codeV` for north and south
  colours, `codeH` for east and west colours); `Letter.toTile` is the tile with these codes.
  **[choice]** This is the relabelling of colours by natural numbers allowed by `set:def-wang`
  (`Tile` has `ℕ` colours). Codes are injective, so matching of tiles is matching of letters.
* `scaffoldSet`: `𝔸` as a `WangSet`; `card_scaffoldSet` (276 tiles) and `scaffold_tiles`
  (`prop:scaffold`: `𝔸` tiles, from `σⁿ` and `set:compact`); `exists_letter_tiling`.
* `fit_pairs_count`: the cross-check with the corner-lemma programs (4496 compatible directional
  pairs), computed in the kernel through the codes.

**Format for the corner-lemma certificate (Part E).** Letters are `Fin 276` indices into
`Letter.letters`; the four side codes `Letter.codeN/E/S/W` (all `< 64`) are the edge colours; two
letters fit in direction `e₁` iff `codeE a = codeW b`, and in direction `e₂` iff
`codeN a = codeS b` (`codeE_eq_codeW_iff`, `codeN_eq_codeS_iff`). Sets of letters will be
276-bit masks (`Nat`), and the fit relation per letter a mask computed from the colour classes.
-/
import FixedNoiseErgodicity.Scaffold.Substitution

set_option autoImplicit false

set_option maxRecDepth 20000

namespace FNE.Scaffold

/-! ## Colour codes -/

/-- The code of a vertical atom. -/
def VAtom.code : VAtom → ℕ
  | .r0 => 0 | .r2 => 1 | .g0 => 2 | .g2 => 3

/-- The code of a horizontal atom. -/
def HAtom.code : HAtom → ℕ
  | .r1 => 0 | .r3 => 1 | .g1 => 2 | .g3 => 3

theorem VAtom.code_lt (a : VAtom) : a.code < 4 := by cases a <;> decide

theorem HAtom.code_lt (a : HAtom) : a.code < 4 := by cases a <;> decide

theorem VAtom.code_injective : Function.Injective VAtom.code := by decide

theorem HAtom.code_injective : Function.Injective HAtom.code := by decide

/-- The code of a north or south colour `((∂θ, ∂κ, ∂ω), b₁)`. -/
def codeV (c : (VAtom × VAtom × Bool) × Bool) : ℕ :=
  c.1.1.code + 4 * c.1.2.1.code + 16 * c.1.2.2.toNat + 32 * c.2.toNat

/-- The code of an east or west colour `((∂θ, ∂κ, ∂ω), b₂)`. -/
def codeH (c : (HAtom × HAtom × Bool) × Bool) : ℕ :=
  c.1.1.code + 4 * c.1.2.1.code + 16 * c.1.2.2.toNat + 32 * c.2.toNat

theorem bool_eq_of_toNat_eq {x y : Bool} (h : x.toNat = y.toNat) : x = y := by
  cases x <;> cases y <;> simp_all

theorem codeV_injective : Function.Injective codeV := by
  rintro ⟨⟨a, b, x⟩, y⟩ ⟨⟨a', b', x'⟩, y'⟩ h
  simp only [codeV] at h
  have := a.code_lt; have := b.code_lt; have := a'.code_lt; have := b'.code_lt
  have := x.toNat_lt; have := y.toNat_lt; have := x'.toNat_lt; have := y'.toNat_lt
  rw [VAtom.code_injective (show a.code = a'.code by omega),
    VAtom.code_injective (show b.code = b'.code by omega),
    bool_eq_of_toNat_eq (show x.toNat = x'.toNat by omega),
    bool_eq_of_toNat_eq (show y.toNat = y'.toNat by omega)]

theorem codeH_injective : Function.Injective codeH := by
  rintro ⟨⟨a, b, x⟩, y⟩ ⟨⟨a', b', x'⟩, y'⟩ h
  simp only [codeH] at h
  have := a.code_lt; have := b.code_lt; have := a'.code_lt; have := b'.code_lt
  have := x.toNat_lt; have := y.toNat_lt; have := x'.toNat_lt; have := y'.toNat_lt
  rw [HAtom.code_injective (show a.code = a'.code by omega),
    HAtom.code_injective (show b.code = b'.code by omega),
    bool_eq_of_toNat_eq (show x.toNat = x'.toNat by omega),
    bool_eq_of_toNat_eq (show y.toNat = y'.toNat by omega)]

namespace Letter

/-- The north colour code of a letter. -/
def codeN (x : Letter) : ℕ := codeV x.colN

/-- The east colour code of a letter. -/
def codeE (x : Letter) : ℕ := codeH x.colE

/-- The south colour code of a letter. -/
def codeS (x : Letter) : ℕ := codeV x.colS

/-- The west colour code of a letter. -/
def codeW (x : Letter) : ℕ := codeH x.colW

theorem codeE_eq_codeW_iff {x y : Letter} : x.codeE = y.codeW ↔ x.MatchE y :=
  codeH_injective.eq_iff

theorem codeN_eq_codeS_iff {x y : Letter} : x.codeN = y.codeS ↔ x.MatchN y :=
  codeV_injective.eq_iff

/-- A letter as a Wang tile, with its four colour codes. -/
def toTile (x : Letter) : Tile := ⟨x.codeN, x.codeE, x.codeS, x.codeW⟩

theorem toTile_injective : Function.Injective toTile := fun _ _ h =>
  col_injective (codeV_injective (congrArg Tile.N h)) (codeV_injective (congrArg Tile.S h))
    (codeH_injective (congrArg Tile.E h)) (codeH_injective (congrArg Tile.W h))

theorem tileH_toTile {x y : Letter} : TileH x.toTile y.toTile ↔ x.MatchE y :=
  codeE_eq_codeW_iff

theorem tileV_toTile {x y : Letter} : TileV x.toTile y.toTile ↔ x.MatchN y :=
  codeN_eq_codeS_iff

end Letter

/-! ## The Wang set `𝔸` -/

/-- `prop:scaffold`: the scaffold `𝔸` as a Wang set (the tiles of its 276 letters). -/
def scaffoldSet : WangSet := (Letter.letters.map Letter.toTile).toFinset

theorem mem_scaffoldSet {t : Tile} : t ∈ scaffoldSet ↔ ∃ x : Letter, x.InA ∧ x.toTile = t := by
  simp [scaffoldSet, Letter.mem_letters]

/-- `prop:scaffold`: `𝔸` is a Wang set of 276 letters. -/
theorem card_scaffoldSet : scaffoldSet.card = 276 := by
  rw [scaffoldSet, List.toFinset_card_of_nodup
    (Letter.letters_nodup.map Letter.toTile_injective), List.length_map, Letter.letters_length]

/-- The index-0 letter `(a, ∠b, A, 0, 0)` (§6 opening paragraph) lies in `𝔸`. -/
theorem index0_inA : (⟨⟨.a, .corner .b, .A⟩, false, false⟩ : Letter).InA := by decide

/-- A legal pattern of letters of `𝔸` gives a legal pattern of the Wang set `𝔸`. -/
theorem isLegalPattern_toTile {U : Set Plane} {w : Plane → Letter} (hA : ∀ u ∈ U, (w u).InA)
    (hw : LegalOn Letter.MatchE Letter.MatchN U w) :
    IsLegalPattern scaffoldSet U (Letter.toTile ∘ w) :=
  ⟨fun u hu => mem_scaffoldSet.2 ⟨w u, hA u hu, rfl⟩,
    hw.map _ (fun _ _ h => Letter.tileH_toTile.2 h) (fun _ _ h => Letter.tileV_toTile.2 h)⟩

/-- `prop:scaffold`: `𝔸` tiles. By `prop:scaffold`(i) every square carries a legal pattern
(a restriction of some `σⁿ(𝔞)`), and `set:compact` (König) gives a tiling. -/
theorem scaffold_tiles : Tiles scaffoldSet := by
  refine tiles_of_forall_square fun m => ?_
  have h := sigmaPow_legal index0_inA m
  have hm : square 0 m ⊆ sq m := square_mono (Nat.lt_pow_self (by norm_num)).le
  exact ⟨0, _, (isLegalPattern_toTile h.1 h.2).mono hm⟩

/-- A tiling of `𝔸` as a map into letters: there is `f : ℤ² → 𝔸` that matches on every edge
(used in §6, `fam:tower-exists`: "take any tiling `f`"). -/
theorem exists_letter_tiling :
    ∃ f : Plane → Letter, (∀ u, (f u).InA) ∧ LegalOn Letter.MatchE Letter.MatchN Set.univ f := by
  obtain ⟨z, hzR, hzE, hzN⟩ := scaffold_tiles
  choose f hfA hfz using fun u => mem_scaffoldSet.1 (hzR u)
  refine ⟨f, hfA, fun u _ _ => ?_, fun u _ _ => ?_⟩
  · rw [← Letter.tileH_toTile, TileH, hfz, hfz]; exact hzE u
  · rw [← Letter.tileV_toTile, TileV, hfz, hfz]; exact hzN u

/-! ## Cross-check with the corner-lemma programs -/

/-- `VERIFY.md` of the corner lemma: of the `4 · 276²` directional pairs of letters, 4496 are
compatible; that is, `2 · (#e₁-matching pairs + #e₂-matching pairs) = 4496` (a pair fits in
direction `-e` iff the reversed pair fits in direction `e`). Computed in the kernel through the
colour codes. -/
theorem fit_pairs_count :
    2 * ((Letter.letters.flatMap fun x => Letter.letters.filter fun y => decide (x.MatchE y)).length
      + (Letter.letters.flatMap fun x =>
        Letter.letters.filter fun y => decide (x.MatchN y)).length) = 4496 := by
  have hE : ∀ x y : Letter, decide (x.MatchE y) = (x.codeE == y.codeW) := by
    intro x y
    rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, Letter.codeE_eq_codeW_iff]
  have hN : ∀ x y : Letter, decide (x.MatchN y) = (x.codeN == y.codeS) := by
    intro x y
    rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, Letter.codeN_eq_codeS_iff]
  simp only [hE, hN]
  decide +kernel

end FNE.Scaffold
