/-
# Section 8 (first half): the palettes of `def:family` decided on explicit lists

`familyR M` filters the candidates `ftileList M` by membership in `R_M` (classical decidability).
Here every palette is replaced, on the candidates, by a check on explicit lists, and `familyR` is
rewritten in a form that `Family/Computable.lean` proves primitive recursive.

* Payloads of `C_M^4` are quadruples of sublists of `𝒰_M` (`Quad`, `quads`, `payList_eq`).
* The seed tile does not depend on `M` (`seedTile_indep`: it reads `𝒞_t(x)` for `t, x ≤ 1` only).
* **A decidable `T_M`** (`inT_iff`): a payload `c ∈ C_M^4` lies in `T_M` iff the block read off its
  west and east colours (`recSite`: the facts at `y ∈ Λ` are those of `(h, y, F) ∈ 𝐜_E` for
  `y₁ ≥ 0` and of `(h, y + e₁, F) ∈ 𝐜_W` for `y₁ < 0`) is legal (`SatAtL`, the clauses (H1)–(H9) at
  the nine sites of `Λ`, with finite quantifiers) and has tile `c`. If `c = tile(Θ)` with `Θ`
  legal, the block read off `c` is `Θ` on `Λ`.
* `palette_iff`: on the candidates, each palette is a check on lists (`PalChk`).
* `familyR_eq`: `familyR M = famC M`, the same list, written as a `filterMap` per routed tile.

**[choice]** `T_M` is decided by reading the block off the payload (no search over blocks). The
clause instances of (H8) range over the symbols of the facts present (`syms`), which is equivalent
to the printed `∀ a, b, c` (`satAt_iff`).
-/
import FixedNoiseErgodicity.Family.FamilyR

set_option autoImplicit false

noncomputable section

namespace FNE.Family

open FNE

/-! ## Payloads as quadruples of lists -/

/-- A payload given by four lists of triples `(W, E, S, N)`. -/
abbrev Quad := List Atom × List Atom × List Atom × List Atom

/-- The payload of a quadruple of lists: the sets of their entries. -/
def toPay (q : Quad) : Pay := ⟨q.1.toFinset, q.2.1.toFinset, q.2.2.1.toFinset, q.2.2.2.toFinset⟩

/-- `C_M^4` as quadruples of sublists of `𝒰_M`, in the order of `payList`. -/
def quads (M : TuringMachine) : List Quad :=
  (uList M).sublists.flatMap fun w => (uList M).sublists.flatMap fun e =>
    (uList M).sublists.flatMap fun s => (uList M).sublists.map fun n => (w, e, s, n)

theorem payList_eq (M : TuringMachine) : payList M = (quads M).map toPay := by
  simp [payList, colourList, quads, List.flatMap_map, List.map_flatMap, Function.comp_def, toPay]

theorem inC_of_mem_quads {M : TuringMachine} {q : Quad} (hq : q ∈ quads M) :
    InC M (toPay q).W ∧ InC M (toPay q).E ∧ InC M (toPay q).S ∧ InC M (toPay q).N := by
  have hs : ∀ l ∈ (uList M).sublists, InC M l.toFinset := fun l hl x hx =>
    mem_uList.1 ((List.mem_sublists.1 hl).subset (List.mem_toFinset.1 hx))
  simp only [quads, List.mem_flatMap, List.mem_map] at hq
  obtain ⟨w, hw, e, he, s, hs', n, hn, rfl⟩ := hq
  exact ⟨hs w hw, hs e he, hs s hs', hs n hn⟩

/-- Two lists with the same entries. -/
def SetEq (l l' : List Atom) : Prop := (∀ x ∈ l, x ∈ l') ∧ ∀ x ∈ l', x ∈ l

instance (l l' : List Atom) : Decidable (SetEq l l') := inferInstanceAs (Decidable (_ ∧ _))

theorem setEq_iff {l l' : List Atom} : SetEq l l' ↔ l.toFinset = l'.toFinset := by
  simp only [SetEq, Finset.ext_iff, List.mem_toFinset]
  exact ⟨fun h x => ⟨h.1 x, h.2 x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩

/-! ## The seed tile does not depend on `M` -/

theorem CA_indep (M M' : TuringMachine) {t x : ℕ} (ht : t ≤ 1) (hx : x ≤ 1) :
    CA M t x = CA M' t x := by
  interval_cases t <;> interval_cases x <;> rfl

theorem leastField_indep (M M' : TuringMachine) {ξ : Plane} (hξ : ξ ∈ box 1) :
    leastField M ξ = leastField M' ξ := by
  rw [mem_box1] at hξ
  unfold leastField
  by_cases h : 0 ≤ ξ.1 ∧ 0 ≤ ξ.2
  · rw [CA_indep M M' (t := ξ.2.toNat) (x := ξ.1.toNat) (by omega) (by omega)]
  · rw [if_neg h, if_neg h]

/-- `tile(Θ)` reads `Θ` on `Λ` only. -/
theorem tileOf_congr {Θ Θ' : FactField} (h : ∀ y ∈ box 1, Θ y = Θ' y) :
    tileOf Θ = tileOf Θ' := by
  ext x <;> simp only [tileOf, mem_blockW, mem_blockE, mem_blockS, mem_blockN] <;>
    constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
    exact ⟨h1, h2, h3, by first | rwa [← h _ h2] | rwa [h _ h2]⟩

theorem seedTile_indep (M M' : TuringMachine) : seedTile M = seedTile M' :=
  tileOf_congr fun _ hy => leastField_indep M M' hy

/-- The seed tile `s_M` (the same for every `M`). -/
def seed0 : Pay := seedTile ⟨[], []⟩

/-! ## A decidable `T_M` -/

/-- The fact `F` of a triple `(h, y, F)` at the site `y`. -/
def selAt (y : Plane) (x : Atom) : Option Fact :=
  if x.1 = false ∧ x.2.1 = y then some x.2.2 else none

theorem mem_filterMap_selAt {l : List Atom} {y : Plane} {F : Fact} :
    F ∈ l.filterMap (selAt y) ↔ (false, y, F) ∈ l := by
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨⟨b, y', F'⟩, hx, h⟩
    unfold selAt at h
    by_cases hc : b = false ∧ y' = y
    · rw [if_pos hc] at h
      obtain ⟨rfl, rfl⟩ := hc
      cases h
      exact hx
    · rw [if_neg hc] at h; cases h
  · intro h
    exact ⟨(false, y, F), h, by simp [selAt]⟩

/-- The block read off a payload: at `y` the facts of `(h, y, F) ∈ 𝐜_E` if `y₁ ≥ 0`, and of
`(h, y + e₁, F) ∈ 𝐜_W` otherwise. -/
def recSite (q : Quad) (y : Plane) : List Fact :=
  if 0 ≤ y.1 then q.2.1.filterMap (selAt y) else q.1.filterMap (selAt (y + (1, 0)))

theorem mem_recSite {q : Quad} {y : Plane} {F : Fact} :
    F ∈ recSite q y ↔ if 0 ≤ y.1 then (false, y, F) ∈ q.2.1 else (false, y + (1, 0), F) ∈ q.1 := by
  unfold recSite
  split_ifs <;> exact mem_filterMap_selAt

/-- The symbol of a fact `P_b`. -/
def Fact.sym? : Fact → Option MSym
  | .P b => some b
  | _ => none

/-- The symbols `b` of the facts `P_b` of a list. -/
def syms (G : List Fact) : List MSym := G.filterMap Fact.sym?

theorem mem_syms {G : List Fact} {b : MSym} : b ∈ syms G ↔ Fact.P b ∈ G := by
  simp only [syms, List.mem_filterMap]
  constructor
  · rintro ⟨F, hF, h⟩
    cases F with
    | P b' => cases h; exact hF
    | _ => cases h
  · intro h; exact ⟨_, h, rfl⟩

/-- A head cell in a halting state. -/
def haltHead (M : TuringMachine) : MSym → Bool
  | .head q _ => oHalt M q
  | _ => false

/-- The clause instances (H1)–(H9) at a site `ξ ∈ Λ` of a block given by lists, with the
quantifiers of (H8) and (H9) over the facts present. -/
def SatAtL (M : TuringMachine) (G : Plane → List Fact) (ξ : Plane) : Prop :=
  (Fact.seed ∈ G ξ → Fact.P .wall ∈ G ξ) ∧
  (ξ + (1, 0) ∈ lamList → Fact.seed ∈ G ξ → Fact.start ∈ G (ξ + (1, 0))) ∧
  (Fact.start ∈ G ξ → Fact.P (.head .init OSym.blank) ∈ G ξ) ∧
  (ξ + (1, 0) ∈ lamList → Fact.start ∈ G ξ → Fact.ray ∈ G (ξ + (1, 0))) ∧
  (Fact.ray ∈ G ξ → Fact.P (.tape OSym.blank) ∈ G ξ) ∧
  (ξ + (1, 0) ∈ lamList → Fact.ray ∈ G ξ → Fact.ray ∈ G (ξ + (1, 0))) ∧
  (ξ + (0, 1) ∈ lamList → Fact.P .wall ∈ G ξ → Fact.P .wall ∈ G (ξ + (0, 1))) ∧
  (ξ - (1, 0) ∈ lamList → ξ + (1, 0) ∈ lamList → ξ + (0, 1) ∈ lamList →
    ∀ a ∈ syms (G (ξ - (1, 0))), ∀ b ∈ syms (G ξ), ∀ c ∈ syms (G (ξ + (1, 0))),
      Fact.P (next (oTr M) (oHalt M) a b c) ∈ G (ξ + (0, 1))) ∧
  (∀ b ∈ syms (G ξ), haltHead M b = false)

set_option synthInstance.maxSize 1024 in
instance (M : TuringMachine) (G : Plane → List Fact) (ξ : Plane) : Decidable (SatAtL M G ξ) := by
  unfold SatAtL; infer_instance

theorem satAt_iff (M : TuringMachine) (G : Plane → List Fact) {ξ : Plane} (hξ : ξ ∈ box 1) :
    SatAt M ↑(box 1) (fun y => (G y).toFinset) ξ ↔ SatAtL M G ξ := by
  have hmem : ∀ y : Plane, y ∈ (↑(box 1) : Set Plane) ↔ y ∈ lamList := fun y => by
    rw [Finset.mem_coe, mem_lamList]
  have hl : ξ ∈ lamList := mem_lamList.2 hξ
  simp only [SatAt, SatAtL, hmem, List.mem_toFinset, hl, true_implies]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ ?_)))))))
  · simp only [mem_syms]
    constructor
    · intro h h1 h2 h3 a ha b hb c hc; exact h h1 h2 h3 a b c ha hb hc
    · intro h h1 h2 h3 a b c ha hb hc; exact h h1 h2 h3 a ha b hb c hc
  · constructor
    · intro h b hb
      rw [mem_syms] at hb
      cases b with
      | head q γ =>
        cases hq : oHalt M q
        · simp [haltHead, hq]
        · exact absurd hb (h q γ hq)
      | wall => rfl
      | tape γ => rfl
    · intro h q γ hq hmem
      have := h _ (mem_syms.2 hmem)
      simp [haltHead, hq] at this

theorem sat_iff (M : TuringMachine) (G : Plane → List Fact) :
    Sat M ↑(box 1) (fun y => (G y).toFinset) ↔ ∀ ξ ∈ lamList, SatAtL M G ξ := by
  constructor
  · intro h ξ hξ; exact (satAt_iff M G (mem_lamList.1 hξ)).1 (h ξ)
  · intro h ξ
    by_cases hξ : ξ ∈ box 1
    · exact (satAt_iff M G hξ).2 (h ξ (mem_lamList.2 hξ))
    · exact ⟨fun h' => absurd h' hξ, fun h' => absurd h' hξ, fun h' => absurd h' hξ,
        fun h' => absurd h' hξ, fun h' => absurd h' hξ, fun h' => absurd h' hξ,
        fun h' => absurd h' hξ, fun _ h' => absurd h' hξ, fun h' => absurd h' hξ⟩

/-- The clauses read a block on `Λ` only. -/
theorem SatAt.congr_box {M : TuringMachine} {Θ Θ' : FactField} {ξ : Plane}
    (h : ∀ y ∈ box 1, Θ y = Θ' y) (hs : SatAt M ↑(box 1) Θ ξ) : SatAt M ↑(box 1) Θ' ξ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hs
  refine ⟨fun a => ?_, fun a b => ?_, fun a => ?_, fun a b => ?_, fun a => ?_, fun a b => ?_,
    fun a b => ?_, fun a b c d => ?_, fun a => ?_⟩
  · rw [← h _ a]; exact h1 a
  · rw [← h _ a, ← h _ b]; exact h2 a b
  · rw [← h _ a]; exact h3 a
  · rw [← h _ a, ← h _ b]; exact h4 a b
  · rw [← h _ a]; exact h5 a
  · rw [← h _ a, ← h _ b]; exact h6 a b
  · rw [← h _ a, ← h _ b]; exact h7 a b
  · rw [← h _ a, ← h _ b, ← h _ c, ← h _ d]; exact h8 a b c d
  · rw [← h _ a]; exact h9 a

/-- `Θ_W` as a list. -/
def lsW (G : Plane → List Fact) : List Atom :=
  (lamList.filter fun y => y.1 ≤ 0).flatMap fun y => (G y).map fun F => (false, y + (1, 0), F)

/-- `Θ_E` as a list. -/
def lsE (G : Plane → List Fact) : List Atom :=
  (lamList.filter fun y => 0 ≤ y.1).flatMap fun y => (G y).map fun F => (false, y, F)

/-- `Θ_S` as a list. -/
def lsS (G : Plane → List Fact) : List Atom :=
  (lamList.filter fun y => y.2 ≤ 0).flatMap fun y => (G y).map fun F => (true, y + (0, 1), F)

/-- `Θ_N` as a list. -/
def lsN (G : Plane → List Fact) : List Atom :=
  (lamList.filter fun y => 0 ≤ y.2).flatMap fun y => (G y).map fun F => (true, y, F)

theorem mem_lsE {G : Plane → List Fact} {x : Atom} :
    x ∈ lsE G ↔ x.1 = false ∧ x.2.1 ∈ box 1 ∧ 0 ≤ x.2.1.1 ∧ x.2.2 ∈ G x.2.1 := by
  obtain ⟨b, y, F⟩ := x
  simp only [lsE, List.mem_flatMap, List.mem_filter, List.mem_map, mem_lamList,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨y', ⟨hy, h0⟩, F', hF, rfl, rfl, rfl⟩; exact ⟨rfl, hy, h0, hF⟩
  · rintro ⟨rfl, hy, h0, hF⟩; exact ⟨y, ⟨hy, h0⟩, F, hF, rfl, rfl, rfl⟩

theorem mem_lsN {G : Plane → List Fact} {x : Atom} :
    x ∈ lsN G ↔ x.1 = true ∧ x.2.1 ∈ box 1 ∧ 0 ≤ x.2.1.2 ∧ x.2.2 ∈ G x.2.1 := by
  obtain ⟨b, y, F⟩ := x
  simp only [lsN, List.mem_flatMap, List.mem_filter, List.mem_map, mem_lamList,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨y', ⟨hy, h0⟩, F', hF, rfl, rfl, rfl⟩; exact ⟨rfl, hy, h0, hF⟩
  · rintro ⟨rfl, hy, h0, hF⟩; exact ⟨y, ⟨hy, h0⟩, F, hF, rfl, rfl, rfl⟩

theorem mem_lsW {G : Plane → List Fact} {x : Atom} :
    x ∈ lsW G ↔ x.1 = false ∧ x.2.1 - (1, 0) ∈ box 1 ∧ x.2.1.1 ≤ 1 ∧
      x.2.2 ∈ G (x.2.1 - (1, 0)) := by
  obtain ⟨b, y, F⟩ := x
  simp only [lsW, List.mem_flatMap, List.mem_filter, List.mem_map, mem_lamList,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨y', ⟨hy, h0⟩, F', hF, rfl, rfl, rfl⟩
    refine ⟨rfl, by simpa using hy, by simp; omega, by simpa using hF⟩
  · rintro ⟨rfl, hy, h0, hF⟩
    exact ⟨y - (1, 0), ⟨hy, by simp; omega⟩, F, hF, rfl, sub_add_cancel _ _, rfl⟩

theorem mem_lsS {G : Plane → List Fact} {x : Atom} :
    x ∈ lsS G ↔ x.1 = true ∧ x.2.1 - (0, 1) ∈ box 1 ∧ x.2.1.2 ≤ 1 ∧
      x.2.2 ∈ G (x.2.1 - (0, 1)) := by
  obtain ⟨b, y, F⟩ := x
  simp only [lsS, List.mem_flatMap, List.mem_filter, List.mem_map, mem_lamList,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨y', ⟨hy, h0⟩, F', hF, rfl, rfl, rfl⟩
    refine ⟨rfl, by simpa using hy, by simp; omega, by simpa using hF⟩
  · rintro ⟨rfl, hy, h0, hF⟩
    exact ⟨y - (0, 1), ⟨hy, by simp; omega⟩, F, hF, rfl, sub_add_cancel _ _, rfl⟩

/-- The tile of a block given by lists, as a quadruple of lists. -/
theorem tileOf_lists (G : Plane → List Fact) :
    tileOf (fun y => (G y).toFinset) = toPay (lsW G, lsE G, lsS G, lsN G) := by
  ext x <;> simp only [tileOf, toPay, mem_blockW, mem_blockE, mem_blockS, mem_blockN,
    List.mem_toFinset, mem_lsW, mem_lsE, mem_lsS, mem_lsN]

/-- **A decidable `T_M`**: the block read off the payload is legal and has the payload as its
tile. -/
def ActChk (M : TuringMachine) (q : Quad) : Prop :=
  (∀ ξ ∈ lamList, SatAtL M (recSite q) ξ) ∧ SetEq (lsW (recSite q)) q.1 ∧
    SetEq (lsE (recSite q)) q.2.1 ∧ SetEq (lsS (recSite q)) q.2.2.1 ∧
    SetEq (lsN (recSite q)) q.2.2.2

instance (M : TuringMachine) (q : Quad) : Decidable (ActChk M q) := by
  unfold ActChk; infer_instance

/-- **`T_M` is decidable** on payloads with colours in `C_M`: `c ∈ T_M` iff the block read off `c`
is legal with tile `c`. -/
theorem inT_iff {M : TuringMachine} {q : Quad}
    (hC : InC M (toPay q).W ∧ InC M (toPay q).E ∧ InC M (toPay q).S ∧ InC M (toPay q).N) :
    InT M (toPay q) ↔ ActChk M q := by
  have htile := tileOf_lists (recSite q)
  constructor
  · rintro ⟨Θ, ⟨-, hsat⟩, hΘ⟩
    have hE : ∀ x, x ∈ q.2.1 ↔ x ∈ blockE Θ := fun x => by
      rw [← List.mem_toFinset]; exact Iff.of_eq (congrArg (x ∈ ·) (congrArg Pay.E hΘ).symm)
    have hW : ∀ x, x ∈ q.1 ↔ x ∈ blockW Θ := fun x => by
      rw [← List.mem_toFinset]; exact Iff.of_eq (congrArg (x ∈ ·) (congrArg Pay.W hΘ).symm)
    have hagree : ∀ y ∈ box 1, (recSite q y).toFinset = Θ y := by
      intro y hy
      ext F
      rw [List.mem_toFinset, mem_recSite]
      split_ifs with h0
      · rw [hE, mem_blockE]
        simp [hy, h0]
      · rw [hW, mem_blockW]
        have hy' := (mem_box1 y).1 hy
        simp only [add_sub_cancel_right, hy, true_and, Prod.fst_add]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨by simp; omega, h⟩
    have hsat' : Sat M ↑(box 1) (fun y => (recSite q y).toFinset) := fun ξ =>
      (hsat ξ).congr_box fun y hy => (hagree y hy).symm
    have ht : toPay (lsW (recSite q), lsE (recSite q), lsS (recSite q), lsN (recSite q)) =
        toPay q := by
      rw [← htile, tileOf_congr hagree, hΘ]
    simp only [toPay, Pay.mk.injEq] at ht
    exact ⟨(sat_iff M _).1 hsat', setEq_iff.2 ht.1, setEq_iff.2 ht.2.1, setEq_iff.2 ht.2.2.1,
      setEq_iff.2 ht.2.2.2⟩
  · rintro ⟨hs, h1, h2, h3, h4⟩
    refine ⟨fun y => (recSite q y).toFinset, ⟨?_, (sat_iff M _).2 hs⟩, ?_⟩
    · intro y _ F hF
      rw [List.mem_toFinset, mem_recSite] at hF
      split_ifs at hF
      · exact (hC.2.1 _ (List.mem_toFinset.2 hF)).2
      · exact (hC.1 _ (List.mem_toFinset.2 hF)).2
    · rw [htile]
      simp only [toPay, setEq_iff.1 h1, setEq_iff.1 h2, setEq_iff.1 h3, setEq_iff.1 h4]

/-! ## The palettes on the candidates -/

/-- The palette of a role, checked on a quadruple of lists. -/
def PalChk (M : TuringMachine) : Role → Quad → Prop
  | .inactive, _ => True
  | .horiz, q => SetEq q.1 q.2.1
  | .vert, q => SetEq q.2.2.1 q.2.2.2
  | .active, q => ActChk M q
  | .seed, q => SetEq q.1 seed0.W.toList ∧ SetEq q.2.1 seed0.E.toList ∧
      SetEq q.2.2.1 seed0.S.toList ∧ SetEq q.2.2.2 seed0.N.toList

instance (M : TuringMachine) (ρ : Role) (q : Quad) : Decidable (PalChk M ρ q) := by
  cases ρ <;> unfold PalChk <;> infer_instance

theorem palette_iff {M : TuringMachine} (ρ : Role) {q : Quad} (hq : q ∈ quads M) :
    palette M ρ (toPay q) ↔ PalChk M ρ q := by
  have hC := inC_of_mem_quads hq
  cases ρ with
  | inactive => exact ⟨fun _ => trivial, fun _ => hC⟩
  | horiz => exact ⟨fun h => setEq_iff.2 h.2, fun h => ⟨hC, setEq_iff.1 h⟩⟩
  | vert => exact ⟨fun h => setEq_iff.2 h.2, fun h => ⟨hC, setEq_iff.1 h⟩⟩
  | active => exact inT_iff hC
  | seed =>
    show toPay q = seedTile M ↔ _
    rw [seedTile_indep M ⟨[], []⟩]
    simp only [PalChk, setEq_iff, Finset.toList_toFinset, toPay, Pay.ext_iff, seed0]

/-! ## `familyR`, palette by palette -/

/-- The tile `FTile.toTile ⟨r, toPay q⟩`, with the payload colours coded from the lists. -/
def tileCode (r : RTile) (q : Quad) : Tile :=
  ⟨Nat.pair (Encodable.encode (r.q.colN, r.fN)) (colCodeL q.2.2.2),
    Nat.pair (Encodable.encode (r.q.colE, r.fE)) (colCodeL q.2.1),
    Nat.pair (Encodable.encode (r.q.colS, r.fS)) (colCodeL q.2.2.1),
    Nat.pair (Encodable.encode (r.q.colW, r.fW)) (colCodeL q.1)⟩

theorem toTile_toPay (r : RTile) (q : Quad) : (FTile.mk r (toPay q)).toTile = tileCode r q := by
  simp only [FTile.toTile, tileCode, colCodeL_eq, toPay]

theorem map_filter_eq_filterMap {α β : Type*} (p : α → Bool) (f : α → β) (l : List α) :
    (l.filter p).map f = l.filterMap fun a => if p a then some (f a) else none := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

open Classical in
/-- `R_M` written routed tile by routed tile, each palette checked on lists. -/
def famC (M : TuringMachine) : List Tile :=
  rtileList.flatMap fun r => if r.InR then
    (quads M).filterMap fun q => if PalChk M r.role q then some (tileCode r q) else none
  else []

theorem familyR_eq (M : TuringMachine) : familyR M = famC M := by
  classical
  unfold familyR famC ftileList
  rw [List.filter_flatMap, List.map_flatMap]
  refine congrArg (fun g => rtileList.flatMap g) (funext fun r => ?_)
  rw [payList_eq, List.map_map, List.filter_map, List.map_map, map_filter_eq_filterMap]
  by_cases hr : r.InR
  · rw [if_pos hr]
    refine List.filterMap_congr fun q hq => ?_
    have : (FTile.mk r (toPay q)).InR M ↔ PalChk M r.role q :=
      ⟨fun h => (palette_iff _ hq).1 h.2, fun h => ⟨hr, (palette_iff _ hq).2 h⟩⟩
    simp only [Function.comp_apply, this, toTile_toPay]
    split_ifs <;> simp_all
  · rw [if_neg hr]
    rw [List.filterMap_eq_nil_iff]
    intro q _
    have : ¬ (FTile.mk r (toPay q)).InR M := fun h => hr h.1
    simp [this]

end FNE.Family
