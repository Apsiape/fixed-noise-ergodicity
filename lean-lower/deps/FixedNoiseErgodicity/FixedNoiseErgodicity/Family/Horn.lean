/-
# Section 6.6: the pointed Horn layer (facts, clauses, the Wang presentation, `prop:horn`)

* `Fact` (`ℋ_M`, with `InH` the restriction to the finite set of facts of `M`), fact fields,
  the clause instances (H1)–(H9) (`SatAt`), legal fact blocks (`LegalFB`), colours `C_M`
  (finite sets of triples `(h/v, y, F)`; `InC` the restriction to `𝒰_M`), the tile of a block
  (`tileOf`), `T_M` (`InT`), the least field `𝖦_M` (`leastField`), the seed tile `s_M`.
* **`prop:horn`(b)** (`horn_b`): if `M` does not halt, `T_M` has a tiling `Υ` with
  `Υ(0,0) = s_M`. `seedTile_inT`: `s_M ∈ T_M` (part of `prop:horn`(a)).

**[choice]** A fact field is a map `ℤ² → Finset Fact`; a block is read on `Λ = V_1` only (values
outside `Λ` are ignored by legality and by `tileOf`). The facts of `M` are the elements of
`Fact` satisfying `InH M` (`P_b` with `b ∈ 𝒮_M`); a legal block takes its facts in `ℋ_M`.
A colour is a `Finset (Bool × ℤ² × Fact)`: `false` is `h`, `true` is `v`.
-/
import FixedNoiseErgodicity.Family.Machine

set_option autoImplicit false

namespace FNE.Family

open FNE

/-- 06:283: the symbols `𝒮_M` of the cellular automaton of `M°` (as a type; the finite set is
`InS (bnd M)`). -/
abbrev MSym := CASym OState OSym

/-- 06:292: facts: `Seed`, `Start`, `Ray` and `P_b`. -/
inductive Fact where
  | seed
  | start
  | ray
  | P (b : MSym)
  deriving DecidableEq

/-- 06:292: `ℋ_M = {Seed, Start, Ray} ∪ {P_b : b ∈ 𝒮_M}`. -/
def InH (M : TuringMachine) : Fact → Prop
  | .P b => InS (bnd M) b
  | _ => True

/-- A fact field (06:292), read on its domain. -/
abbrev FactField := Plane → Finset Fact

/-- 06:293–299: the clause instances (H1)–(H9) at the site `ξ`, for a fact field `G` on `V`: an
instance is required only when every site it mentions lies in `V`. -/
def SatAt (M : TuringMachine) (V : Set Plane) (G : FactField) (ξ : Plane) : Prop :=
  (ξ ∈ V → Fact.seed ∈ G ξ → Fact.P .wall ∈ G ξ) ∧
  (ξ ∈ V → ξ + (1, 0) ∈ V → Fact.seed ∈ G ξ → Fact.start ∈ G (ξ + (1, 0))) ∧
  (ξ ∈ V → Fact.start ∈ G ξ → Fact.P (.head .init OSym.blank) ∈ G ξ) ∧
  (ξ ∈ V → ξ + (1, 0) ∈ V → Fact.start ∈ G ξ → Fact.ray ∈ G (ξ + (1, 0))) ∧
  (ξ ∈ V → Fact.ray ∈ G ξ → Fact.P (.tape OSym.blank) ∈ G ξ) ∧
  (ξ ∈ V → ξ + (1, 0) ∈ V → Fact.ray ∈ G ξ → Fact.ray ∈ G (ξ + (1, 0))) ∧
  (ξ ∈ V → ξ + (0, 1) ∈ V → Fact.P .wall ∈ G ξ → Fact.P .wall ∈ G (ξ + (0, 1))) ∧
  (ξ - (1, 0) ∈ V → ξ ∈ V → ξ + (1, 0) ∈ V → ξ + (0, 1) ∈ V → ∀ a b c : MSym,
    Fact.P a ∈ G (ξ - (1, 0)) → Fact.P b ∈ G ξ → Fact.P c ∈ G (ξ + (1, 0)) →
      Fact.P (next (oTr M) (oHalt M) a b c) ∈ G (ξ + (0, 1))) ∧
  (ξ ∈ V → ∀ (q : OState) (γ : OSym), oHalt M q = true → Fact.P (.head q γ) ∉ G ξ)

/-- A fact field on `V` satisfies every clause instance that mentions only sites of `V`. -/
def Sat (M : TuringMachine) (V : Set Plane) (G : FactField) : Prop := ∀ ξ, SatAt M V G ξ

theorem SatAt.mono {M : TuringMachine} {V V' : Set Plane} {G : FactField} {ξ : Plane}
    (h : SatAt M V G ξ) (hV : V' ⊆ V) : SatAt M V' G ξ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨fun a => h1 (hV a), fun a b => h2 (hV a) (hV b), fun a => h3 (hV a),
    fun a b => h4 (hV a) (hV b), fun a => h5 (hV a), fun a b => h6 (hV a) (hV b),
    fun a b => h7 (hV a) (hV b), fun a b c d => h8 (hV a) (hV b) (hV c) (hV d), fun a => h9 (hV a)⟩

/-- A model's clause instance at `u + ξ` is the instance at `ξ` of the translated field. -/
theorem SatAt.translate {M : TuringMachine} {G : FactField} {u ξ : Plane}
    (h : SatAt M Set.univ G (u + ξ)) (V : Set Plane) : SatAt M V (fun y => G (u + y)) ξ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have e1 : u + (ξ + (1, 0)) = u + ξ + (1, 0) := (add_assoc _ _ _).symm
  have e2 : u + (ξ + (0, 1)) = u + ξ + (0, 1) := (add_assoc _ _ _).symm
  have e3 : u + (ξ - (1, 0)) = u + ξ - (1, 0) := (add_sub_assoc _ _ _).symm
  refine ⟨fun _ => h1 trivial, fun _ _ => ?_, fun _ => h3 trivial, fun _ _ => ?_,
    fun _ => h5 trivial, fun _ _ => ?_, fun _ _ => ?_, fun _ _ _ _ => ?_, fun _ => h9 trivial⟩
  · simp only [e1]; exact h2 trivial trivial
  · simp only [e1]; exact h4 trivial trivial
  · simp only [e1]; exact h6 trivial trivial
  · simp only [e2]; exact h7 trivial trivial
  · simp only [e1, e2, e3]; exact h8 trivial trivial trivial trivial

/-- 06:301: a *legal fact block*: a fact field on `Λ` (with facts in `ℋ_M`) that satisfies every
clause instance mentioning only sites of `Λ`. -/
def LegalFB (M : TuringMachine) (Θ : FactField) : Prop :=
  (∀ y ∈ box 1, ∀ F ∈ Θ y, InH M F) ∧ Sat M ↑(box 1) Θ

/-- 06:301: a colour of `C_M`: a set of triples `(h/v, y, F)` (`false` is `h`, `true` is `v`). -/
abbrev Colour := Finset (Bool × Plane × Fact)

/-- 06:301: `C_M = 2^{𝒰_M}` with `𝒰_M = {h, v} × Λ × ℋ_M`: the colours with sites in `Λ` and
facts in `ℋ_M`. -/
def InC (M : TuringMachine) (c : Colour) : Prop := ∀ x ∈ c, x.2.1 ∈ box 1 ∧ InH M x.2.2

/-- A payload `(𝐜_W, 𝐜_E, 𝐜_S, 𝐜_N) ∈ C_M^4`. -/
@[ext] structure Pay where
  /-- west colour -/
  W : Colour
  /-- east colour -/
  E : Colour
  /-- south colour -/
  S : Colour
  /-- north colour -/
  N : Colour
  deriving DecidableEq

/-- `Λ = V_1`, as a computable finite set (equal to `box 1`, which `Statements.lean` defines in a
noncomputable section). -/
def lam : Finset Plane :=
  {(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)}

theorem lam_eq : lam = box 1 := by
  ext ⟨a, b⟩
  simp only [lam, box, Finset.mem_insert, Finset.mem_singleton, Finset.mem_product,
    Finset.mem_Icc, Prod.mk.injEq]
  omega

/-- `Θ_E = {(h, y, F) : y ∈ Λ, y₁ ≥ 0, F ∈ Θ(y)}`. -/
def blockE (Θ : FactField) : Colour :=
  (lam.filter fun y => 0 ≤ y.1).biUnion fun y => (Θ y).image fun F => (false, y, F)

/-- `Θ_W = {(h, y + e₁, F) : y ∈ Λ, y₁ ≤ 0, F ∈ Θ(y)}`. -/
def blockW (Θ : FactField) : Colour :=
  (lam.filter fun y => y.1 ≤ 0).biUnion fun y => (Θ y).image fun F => (false, y + (1, 0), F)

/-- `Θ_N = {(v, y, F) : y ∈ Λ, y₂ ≥ 0, F ∈ Θ(y)}`. -/
def blockN (Θ : FactField) : Colour :=
  (lam.filter fun y => 0 ≤ y.2).biUnion fun y => (Θ y).image fun F => (true, y, F)

/-- `Θ_S = {(v, y + e₂, F) : y ∈ Λ, y₂ ≤ 0, F ∈ Θ(y)}`. -/
def blockS (Θ : FactField) : Colour :=
  (lam.filter fun y => y.2 ≤ 0).biUnion fun y => (Θ y).image fun F => (true, y + (0, 1), F)

/-- 06:301: `tile(Θ) = (Θ_W, Θ_E, Θ_S, Θ_N)`. -/
def tileOf (Θ : FactField) : Pay := ⟨blockW Θ, blockE Θ, blockS Θ, blockN Θ⟩

/-- 06:301: `T_M`, the tiles of the legal fact blocks. -/
def InT (M : TuringMachine) (c : Pay) : Prop := ∃ Θ, LegalFB M Θ ∧ tileOf Θ = c

theorem mem_box1 (y : Plane) : y ∈ box 1 ↔ -1 ≤ y.1 ∧ y.1 ≤ 1 ∧ -1 ≤ y.2 ∧ y.2 ≤ 1 := by
  simp [box, Finset.mem_product, and_assoc]

theorem mem_blockE {Θ : FactField} {x : Bool × Plane × Fact} :
    x ∈ blockE Θ ↔ x.1 = false ∧ x.2.1 ∈ box 1 ∧ 0 ≤ x.2.1.1 ∧ x.2.2 ∈ Θ x.2.1 := by
  obtain ⟨b, y, F⟩ := x
  simp only [blockE, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image, Prod.mk.injEq, lam_eq]
  constructor
  · rintro ⟨y', ⟨hy, h0⟩, F', hF, rfl, rfl, rfl⟩; exact ⟨rfl, hy, h0, hF⟩
  · rintro ⟨rfl, hy, h0, hF⟩; exact ⟨y, ⟨hy, h0⟩, F, hF, rfl, rfl, rfl⟩

theorem mem_blockN {Θ : FactField} {x : Bool × Plane × Fact} :
    x ∈ blockN Θ ↔ x.1 = true ∧ x.2.1 ∈ box 1 ∧ 0 ≤ x.2.1.2 ∧ x.2.2 ∈ Θ x.2.1 := by
  obtain ⟨b, y, F⟩ := x
  simp only [blockN, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image, Prod.mk.injEq, lam_eq]
  constructor
  · rintro ⟨y', ⟨hy, h0⟩, F', hF, rfl, rfl, rfl⟩; exact ⟨rfl, hy, h0, hF⟩
  · rintro ⟨rfl, hy, h0, hF⟩; exact ⟨y, ⟨hy, h0⟩, F, hF, rfl, rfl, rfl⟩

theorem mem_blockW {Θ : FactField} {x : Bool × Plane × Fact} :
    x ∈ blockW Θ ↔ x.1 = false ∧ x.2.1 - (1, 0) ∈ box 1 ∧ x.2.1.1 ≤ 1 ∧
      x.2.2 ∈ Θ (x.2.1 - (1, 0)) := by
  obtain ⟨b, y, F⟩ := x
  simp only [blockW, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image, Prod.mk.injEq, lam_eq]
  constructor
  · rintro ⟨y', ⟨hy, h0⟩, F', hF, rfl, rfl, rfl⟩
    refine ⟨rfl, by simpa using hy, by simp; omega, by simpa using hF⟩
  · rintro ⟨rfl, hy, h0, hF⟩
    exact ⟨y - (1, 0), ⟨hy, by simp; omega⟩, F, hF, rfl, sub_add_cancel _ _, rfl⟩

theorem mem_blockS {Θ : FactField} {x : Bool × Plane × Fact} :
    x ∈ blockS Θ ↔ x.1 = true ∧ x.2.1 - (0, 1) ∈ box 1 ∧ x.2.1.2 ≤ 1 ∧
      x.2.2 ∈ Θ (x.2.1 - (0, 1)) := by
  obtain ⟨b, y, F⟩ := x
  simp only [blockS, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image, Prod.mk.injEq, lam_eq]
  constructor
  · rintro ⟨y', ⟨hy, h0⟩, F', hF, rfl, rfl, rfl⟩
    refine ⟨rfl, by simpa using hy, by simp; omega, by simpa using hF⟩
  · rintro ⟨rfl, hy, h0, hF⟩
    exact ⟨y - (0, 1), ⟨hy, by simp; omega⟩, F, hF, rfl, sub_add_cancel _ _, rfl⟩

/-- 06:301 (overlap property): translates of one field match east to west. -/
theorem tileOf_matchE (G : FactField) (u : Plane) :
    (tileOf fun y => G (u + y)).E = (tileOf fun y => G (u + (1, 0) + y)).W := by
  ext ⟨b, y, F⟩
  simp only [tileOf, mem_blockE, mem_blockW, mem_box1]
  have e : u + (1, 0) + (y - (1, 0)) = u + y := by abel
  rw [e]
  simp only [Prod.fst_sub, Prod.snd_sub, sub_zero]
  constructor
  · rintro ⟨h1, ⟨a, b, c, d⟩, h0, hF⟩; exact ⟨h1, ⟨by omega, by omega, c, d⟩, by omega, hF⟩
  · rintro ⟨h1, ⟨a, b, c, d⟩, h0, hF⟩; exact ⟨h1, ⟨by omega, by omega, c, d⟩, by omega, hF⟩

/-- 06:301 (overlap property): translates of one field match north to south. -/
theorem tileOf_matchN (G : FactField) (u : Plane) :
    (tileOf fun y => G (u + y)).N = (tileOf fun y => G (u + (0, 1) + y)).S := by
  ext ⟨b, y, F⟩
  simp only [tileOf, mem_blockN, mem_blockS, mem_box1]
  have e : u + (0, 1) + (y - (0, 1)) = u + y := by abel
  rw [e]
  simp only [Prod.fst_sub, Prod.snd_sub, sub_zero]
  constructor
  · rintro ⟨h1, ⟨a, b, c, d⟩, h0, hF⟩; exact ⟨h1, ⟨a, b, by omega, by omega⟩, by omega, hF⟩
  · rintro ⟨h1, ⟨a, b, c, d⟩, h0, hF⟩; exact ⟨h1, ⟨a, b, by omega, by omega⟩, by omega, hF⟩

/-- The colours of a tile of `T_M` lie in `C_M`. -/
theorem InT.inC {M : TuringMachine} {c : Pay} (h : InT M c) :
    InC M c.W ∧ InC M c.E ∧ InC M c.S ∧ InC M c.N := by
  obtain ⟨Θ, ⟨hH, -⟩, rfl⟩ := h
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [tileOf, mem_blockW] at hx
    obtain ⟨-, hy, h1, hF⟩ := hx
    refine ⟨?_, hH _ hy _ hF⟩
    rw [mem_box1] at hy ⊢; simp only [Prod.fst_sub, Prod.snd_sub, sub_zero] at hy; omega
  · rw [tileOf, mem_blockE] at hx
    exact ⟨hx.2.1, hH _ hx.2.1 _ hx.2.2.2⟩
  · rw [tileOf, mem_blockS] at hx
    obtain ⟨-, hy, h1, hF⟩ := hx
    refine ⟨?_, hH _ hy _ hF⟩
    rw [mem_box1] at hy ⊢; simp only [Prod.fst_sub, Prod.snd_sub, sub_zero] at hy; omega
  · rw [tileOf, mem_blockN] at hx
    exact ⟨hx.2.1, hH _ hx.2.1 _ hx.2.2.2⟩

/-! ## The least field and the seed tile -/

theorem CA_zero_right (M : TuringMachine) (t : ℕ) : CA M t 0 = .wall := by
  simp only [CA]; rw [caRun]

theorem CA_zero_one (M : TuringMachine) : CA M 0 1 = .head .init OSym.blank := by
  simp only [CA]; rw [caRun]

theorem CA_zero_add_two (M : TuringMachine) (x : ℕ) : CA M 0 (x + 2) = .tape OSym.blank := by
  simp only [CA]; rw [caRun]

theorem CA_succ_succ (M : TuringMachine) (t x : ℕ) :
    CA M (t + 1) (x + 1) = next (oTr M) (oHalt M) (CA M t x) (CA M t (x + 1)) (CA M t (x + 2)) := by
  simp only [CA]; rw [caRun]

/-- 06:305: the least field `𝖦_M`: `{Seed, P_𝗐}` at `(0,0)`, `{Start, P_{(𝗊₀,⊔)}}` at `(1,0)`,
`{Ray, P_⊔}` at `(x,0)` for `x ≥ 2`, `{P_𝗐}` at `(0,t)` for `t ≥ 1`, `{P_{𝒞_t(x)}}` at `(x,t)`
for `x, t ≥ 1`, and `∅` elsewhere. Written uniformly: `P_{𝒞_t(x)}` at every `(x, t)` with
`x, t ≥ 0` (`𝒞_t(0) = 𝗐`, `𝒞_0(1) = (𝗊₀, ⊔)`, `𝒞_0(x) = ⊔` for `x ≥ 2`), plus `Seed`,
`Start`, `Ray` on row `0`. -/
def leastField (M : TuringMachine) (ξ : Plane) : Finset Fact :=
  (if 0 ≤ ξ.1 ∧ 0 ≤ ξ.2 then {Fact.P (CA M ξ.2.toNat ξ.1.toNat)} else ∅) ∪
    (if ξ = (0, 0) then {Fact.seed} else ∅) ∪ (if ξ = (1, 0) then {Fact.start} else ∅) ∪
    (if ξ.2 = 0 ∧ 2 ≤ ξ.1 then {Fact.ray} else ∅)

section Least

variable {M : TuringMachine} {ξ : Plane}

@[simp] theorem seed_mem_least : Fact.seed ∈ leastField M ξ ↔ ξ = (0, 0) := by
  unfold leastField; split_ifs <;> simp_all

@[simp] theorem start_mem_least : Fact.start ∈ leastField M ξ ↔ ξ = (1, 0) := by
  unfold leastField; split_ifs <;> simp_all

@[simp] theorem ray_mem_least : Fact.ray ∈ leastField M ξ ↔ ξ.2 = 0 ∧ 2 ≤ ξ.1 := by
  unfold leastField; split_ifs <;> simp_all

@[simp] theorem P_mem_least {b : MSym} :
    Fact.P b ∈ leastField M ξ ↔ 0 ≤ ξ.1 ∧ 0 ≤ ξ.2 ∧ b = CA M ξ.2.toNat ξ.1.toNat := by
  unfold leastField; split_ifs <;> simp_all [eq_comm]

end Least

/-- The facts of `𝖦_M` lie in `ℋ_M`. -/
theorem leastField_inH (M : TuringMachine) (ξ : Plane) (F : Fact) (hF : F ∈ leastField M ξ) :
    InH M F := by
  cases F with
  | P b =>
    obtain ⟨-, -, rfl⟩ := P_mem_least.1 hF
    exact CA_inS M _ _
  | _ => trivial

/-- `prop:horn`, proof of (a) and (b): `𝖦_M` satisfies every instance of (H1)–(H8), and the
instance of (H9) at any site where it carries no halting head. -/
theorem leastField_satAt (M : TuringMachine) (ξ : Plane)
    (h9 : ∀ (q : OState) (γ : OSym), oHalt M q = true → Fact.P (.head q γ) ∉ leastField M ξ) :
    SatAt M Set.univ (leastField M) ξ := by
  obtain ⟨x, t⟩ := ξ
  refine ⟨fun _ h => ?_, fun _ _ h => ?_, fun _ h => ?_, fun _ _ h => ?_, fun _ h => ?_,
    fun _ _ h => ?_, fun _ _ h => ?_, fun _ _ _ _ a b c ha hb hc => ?_, fun _ => h9⟩
  · simp only [seed_mem_least, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [CA_zero_right]
  · simp only [seed_mem_least, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  · simp only [start_mem_least, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [CA_zero_one]
  · simp only [start_mem_least, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  · simp only [ray_mem_least] at h
    obtain ⟨rfl, h2⟩ := h
    rw [P_mem_least]
    refine ⟨by omega, le_rfl, ?_⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, x.toNat = n + 2 := ⟨x.toNat - 2, by omega⟩
    rw [show (0 : ℤ).toNat = 0 from rfl, hn, CA_zero_add_two]
  · simp only [ray_mem_least] at h ⊢
    simp only [Prod.mk_add_mk, add_zero]
    omega
  · simp only [P_mem_least, Prod.mk_add_mk, add_zero] at h ⊢
    obtain ⟨h1, h2, hw⟩ := h
    refine ⟨h1, by omega, ?_⟩
    obtain ⟨s, rfl⟩ : ∃ s : ℕ, t = s := ⟨t.toNat, by omega⟩
    rw [show ((s : ℤ) + 1).toNat = s + 1 by omega]
    rcases Nat.eq_zero_or_pos x.toNat with hx | hx
    · rw [hx, CA_zero_right]
    · obtain ⟨n, hn⟩ : ∃ n, x.toNat = n + 1 := ⟨x.toNat - 1, by omega⟩
      rw [Int.toNat_natCast] at hw
      rw [hn, CA_succ_succ, ← hn, ← hw]; rfl
  · simp only [P_mem_least, Prod.mk_sub_mk, Prod.mk_add_mk, sub_zero, add_zero] at ha hb hc ⊢
    obtain ⟨ha1, ha2, rfl⟩ := ha
    obtain ⟨-, -, rfl⟩ := hb
    obtain ⟨-, -, rfl⟩ := hc
    refine ⟨by omega, by omega, ?_⟩
    obtain ⟨s, rfl⟩ : ∃ s : ℕ, t = s := ⟨t.toNat, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, x = (n + 1 : ℕ) := ⟨(x - 1).toNat, by omega⟩
    rw [show ((s : ℤ) + 1).toNat = s + 1 by omega, show ((n + 1 : ℕ) : ℤ).toNat = n + 1 by omega,
      show ((n + 1 : ℕ) - 1 : ℤ).toNat = n by omega,
      show ((n + 1 : ℕ) + 1 : ℤ).toNat = n + 2 by omega, Int.toNat_natCast, CA_succ_succ]

/-- 06:305: the seed tile `s_M = tile(𝖦_M|_Λ)`. -/
def seedTile (M : TuringMachine) : Pay := tileOf (leastField M)

/-- **`prop:horn`(a)**, the seed tile: `s_M ∈ T_M` (the block `𝖦_M|_Λ` carries no halting head:
`𝗊₀` is not halting and `𝒞_1(1) ∈ Γ`). -/
theorem seedTile_inT (M : TuringMachine) : InT M (seedTile M) := by
  refine ⟨leastField M, ⟨fun y _ F hF => leastField_inH M y F hF, fun ξ => ?_⟩, rfl⟩
  by_cases hξ : ξ ∈ box 1
  · refine (leastField_satAt M ξ fun q γ hq hmem => ?_).mono (Set.subset_univ _)
    rw [P_mem_least] at hmem
    obtain ⟨h1, h2, he⟩ := hmem
    rw [mem_box1] at hξ
    obtain ⟨x, t⟩ := ξ
    simp only at h1 h2 he hξ
    have hx : x.toNat = 0 ∨ x.toNat = 1 := by omega
    have ht : t.toNat = 0 ∨ t.toNat = 1 := by omega
    rcases hx with hx | hx <;> rw [hx] at he
    · rw [CA_zero_right] at he; cases he
    · rcases ht with ht | ht <;> rw [ht] at he
      · rw [CA_zero_one] at he; cases he; rw [oHalt_init] at hq; cases hq
      · obtain ⟨γ', hγ'⟩ := CA_one_one M
        rw [hγ'] at he; cases he
  · refine ⟨fun h => absurd h hξ, fun h => absurd h hξ, fun h => absurd h hξ,
      fun h => absurd h hξ, fun h => absurd h hξ, fun h => absurd h hξ, fun h => absurd h hξ,
      fun _ h => absurd h hξ, fun h => absurd h hξ⟩

/-- **`prop:horn`(b).** If `M` does not halt, `T_M` has a tiling `Υ` with `Υ(0,0) = s_M`:
`Υ(u) = tile(Θ_u)` with `Θ_u(y) = 𝖦_M(u + y)`; `𝖦_M` is a model (with (H9) because no
`𝒞_t(x)` carries a halting state). -/
theorem horn_b (M : TuringMachine) (hM : ¬ M.Halts) :
    ∃ Υ : Plane → Pay, (∀ u, InT M (Υ u)) ∧ (∀ u, (Υ u).E = (Υ (u + (1, 0))).W) ∧
      (∀ u, (Υ u).N = (Υ (u + (0, 1))).S) ∧ Υ (0, 0) = seedTile M := by
  have hsat : Sat M Set.univ (leastField M) := fun ξ =>
    leastField_satAt M ξ fun q γ hq hmem => by
      rw [P_mem_least] at hmem
      have := CA_no_halt M hM _ _ q γ hmem.2.2.symm
      rw [hq] at this; cases this
  refine ⟨fun u => tileOf fun y => leastField M (u + y), fun u => ⟨_, ⟨fun y _ F hF =>
      leastField_inH M _ F hF, fun ξ => (hsat (u + ξ)).translate _⟩, rfl⟩,
    fun u => tileOf_matchE _ u, fun u => tileOf_matchN _ u, ?_⟩
  simp only [zero_add]
  rfl

/-! ## `prop:horn`(a): closure under `∧` -/

/-- 06:301: `∧` on `C_M^4`, the coordinatewise intersection. -/
def Pay.meet (c c' : Pay) : Pay := ⟨c.W ∩ c'.W, c.E ∩ c'.E, c.S ∩ c'.S, c.N ∩ c'.N⟩

/-- `prop:horn`(a), proof: the pointwise intersection of two legal blocks is legal. -/
theorem LegalFB.inter {M : TuringMachine} {Θ Θ' : FactField} (h : LegalFB M Θ)
    (h' : LegalFB M Θ') : LegalFB M fun y => Θ y ∩ Θ' y := by
  refine ⟨fun y hy F hF => h.1 y hy F (Finset.mem_inter.1 hF).1, fun ξ => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h.2 ξ
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h'.2 ξ
  simp only [SatAt, Finset.mem_inter]
  exact ⟨fun v hs => ⟨a1 v hs.1, b1 v hs.2⟩, fun v w hs => ⟨a2 v w hs.1, b2 v w hs.2⟩,
    fun v hs => ⟨a3 v hs.1, b3 v hs.2⟩, fun v w hs => ⟨a4 v w hs.1, b4 v w hs.2⟩,
    fun v hs => ⟨a5 v hs.1, b5 v hs.2⟩, fun v w hs => ⟨a6 v w hs.1, b6 v w hs.2⟩,
    fun v w hs => ⟨a7 v w hs.1, b7 v w hs.2⟩,
    fun v1 v2 v3 v4 a b c ha hb hc =>
      ⟨a8 v1 v2 v3 v4 a b c ha.1 hb.1 hc.1, b8 v1 v2 v3 v4 a b c ha.2 hb.2 hc.2⟩,
    fun v q γ hq hm => a9 v q γ hq hm.1⟩

/-- `prop:horn`(a), proof: `tile(Θ ∩ Θ') = tile(Θ) ∧ tile(Θ')` (every colour is a set of facts
read off the block). -/
theorem tileOf_inter (Θ Θ' : FactField) :
    tileOf (fun y => Θ y ∩ Θ' y) = (tileOf Θ).meet (tileOf Θ') := by
  ext x <;> simp only [tileOf, Pay.meet, Finset.mem_inter, mem_blockW, mem_blockE, mem_blockS,
    mem_blockN] <;> tauto

/-- **`prop:horn`(a)**: `T_M` is closed under `∧`. -/
theorem InT.meet {M : TuringMachine} {c c' : Pay} (h : InT M c) (h' : InT M c') :
    InT M (c.meet c') := by
  obtain ⟨Θ, hΘ, rfl⟩ := h
  obtain ⟨Θ', hΘ', rfl⟩ := h'
  exact ⟨_, hΘ.inter hΘ', tileOf_inter Θ Θ'⟩

/-- **`prop:horn`(a)**: the other palettes are closed under `∧`: `C_M^4`, `{𝐜_W = 𝐜_E}`,
`{𝐜_S = 𝐜_N}`, and `{s_M}` (idempotence). -/
theorem palettes_meet {M : TuringMachine} (c c' : Pay) :
    ((InC M c.W ∧ InC M c.E ∧ InC M c.S ∧ InC M c.N) →
      (InC M c'.W ∧ InC M c'.E ∧ InC M c'.S ∧ InC M c'.N) →
      (InC M (c.meet c').W ∧ InC M (c.meet c').E ∧ InC M (c.meet c').S ∧
        InC M (c.meet c').N)) ∧
    (c.W = c.E → c'.W = c'.E → (c.meet c').W = (c.meet c').E) ∧
    (c.S = c.N → c'.S = c'.N → (c.meet c').S = (c.meet c').N) ∧
    (seedTile M).meet (seedTile M) = seedTile M := by
  refine ⟨fun h h' => ?_, fun h h' => by simp [Pay.meet, h, h'],
    fun h h' => by simp [Pay.meet, h, h'], by ext1 <;> simp [Pay.meet]⟩
  have hi : ∀ {a b : Colour}, InC M a → InC M (a ∩ b) := fun ha x hx =>
    ha x (Finset.mem_inter.1 hx).1
  exact ⟨hi h.1, hi h.2.1, hi h.2.2.1, hi h.2.2.2⟩

end FNE.Family
