/-
# Section 2.1: legal patterns and compactness (`set:def-wang`, `set:compact`)

* `LegalOn H V U p`: a pattern `p` is legal on `U` for matching relations `H` (direction `e₁`) and
  `V` (direction `e₂`). The relations are parameters, so the same notion serves Wang tiles
  (`TileH`, `TileV`) and the letters of the scaffold (§5), whose matching is defined by colours.
  **[choice]** Patterns are total maps `ℤ² → α`; a pattern on `U` is such a map read on `U` only
  (`LegalOn.congr`), and "a pattern of `R` on `U`" adds `∀ u ∈ U, p u ∈ R` (`IsLegalPattern`).
* Restrictions and translates of legal patterns are legal (the remark after `set:def-wang`).
* `set:compact` (König's lemma), proved by compactness of `R^{ℤ²}` (Tychonoff, in Mathlib):
  `tiles_of_forall_box`, `tiles_of_forall_square`, and the printed form `compact`.
-/
import FixedNoiseErgodicity.Section2.TokenGame
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions

set_option autoImplicit false

namespace FNE

open Filter

/-! ## Legal patterns -/

section Legal

variable {α β : Type*}

/-- `set:def-wang`. A pattern `p` is *legal on `U`* (for the matching relations `H` in direction
`e₁` and `V` in direction `e₂`) if `H (p u) (p (u + e₁))` whenever `u, u + e₁ ∈ U`, and
`V (p u) (p (u + e₂))` whenever `u, u + e₂ ∈ U`. -/
def LegalOn (H V : α → α → Prop) (U : Set Plane) (p : Plane → α) : Prop :=
  (∀ u, u ∈ U → u + (1, 0) ∈ U → H (p u) (p (u + (1, 0)))) ∧
  (∀ u, u ∈ U → u + (0, 1) ∈ U → V (p u) (p (u + (0, 1))))

variable {H V : α → α → Prop} {U U' : Set Plane} {p q : Plane → α}

/-- Restrictions of legal patterns are legal. -/
theorem LegalOn.mono (h : LegalOn H V U p) (hU : U' ⊆ U) : LegalOn H V U' p :=
  ⟨fun u hu hu' => h.1 u (hU hu) (hU hu'), fun u hu hu' => h.2 u (hU hu) (hU hu')⟩

/-- Legality on `U` depends only on the values on `U`. -/
theorem LegalOn.congr (h : LegalOn H V U p) (hpq : ∀ u ∈ U, p u = q u) : LegalOn H V U q := by
  refine ⟨fun u hu hu' => ?_, fun u hu hu' => ?_⟩
  · rw [← hpq u hu, ← hpq _ hu']; exact h.1 u hu hu'
  · rw [← hpq u hu, ← hpq _ hu']; exact h.2 u hu hu'

/-- Translates of legal patterns are legal: `u ↦ p (u + a)` is legal on `U - a`. -/
theorem LegalOn.translate (h : LegalOn H V U p) (a : Plane) :
    LegalOn H V {u | u + a ∈ U} (fun u => p (u + a)) := by
  refine ⟨fun u hu hu' => ?_, fun u hu hu' => ?_⟩
  · have e : u + (1, 0) + a = u + a + (1, 0) := add_right_comm _ _ _
    simp only [Set.mem_setOf_eq, e] at hu' ⊢
    exact h.1 _ hu hu'
  · have e : u + (0, 1) + a = u + a + (0, 1) := add_right_comm _ _ _
    simp only [Set.mem_setOf_eq, e] at hu' ⊢
    exact h.2 _ hu hu'

/-- A map that respects the matching relations sends legal patterns to legal patterns. -/
theorem LegalOn.map {H' V' : β → β → Prop} (f : α → β) (hH : ∀ a b, H a b → H' (f a) (f b))
    (hV : ∀ a b, V a b → V' (f a) (f b)) (h : LegalOn H V U p) : LegalOn H' V' U (f ∘ p) :=
  ⟨fun u hu hu' => hH _ _ (h.1 u hu hu'), fun u hu hu' => hV _ _ (h.2 u hu hu')⟩

end Legal

/-- `set:def-wang`. Tiles match in direction `e₁` if `t_E = t'_W`. -/
def TileH (t t' : Tile) : Prop := t.E = t'.W

/-- `set:def-wang`. Tiles match in direction `e₂` if `t_N = t'_S`. -/
def TileV (t t' : Tile) : Prop := t.N = t'.S

/-- `set:def-wang`. A legal pattern of the Wang set `R` on `U`. -/
def IsLegalPattern (R : WangSet) (U : Set Plane) (p : Plane → Tile) : Prop :=
  (∀ u ∈ U, p u ∈ R) ∧ LegalOn TileH TileV U p

/-- `set:def-wang`. A tiling is a legal pattern on `ℤ²`. -/
theorem isTiling_iff_isLegalPattern {R : WangSet} {z : Plane → Tile} :
    IsTiling R z ↔ IsLegalPattern R Set.univ z := by
  simp [IsTiling, IsLegalPattern, LegalOn, TileH, TileV]

theorem IsLegalPattern.mono {R : WangSet} {U U' : Set Plane} {p : Plane → Tile}
    (h : IsLegalPattern R U p) (hU : U' ⊆ U) : IsLegalPattern R U' p :=
  ⟨fun u hu => h.1 u (hU hu), h.2.mono hU⟩

theorem IsLegalPattern.translate {R : WangSet} {U : Set Plane} {p : Plane → Tile}
    (h : IsLegalPattern R U p) (a : Plane) :
    IsLegalPattern R {u | u + a ∈ U} (fun u => p (u + a)) :=
  ⟨fun _ hu => h.1 _ hu, h.2.translate a⟩

/-- The square `a + [0, m)²` of side `m`. -/
def square (a : Plane) (m : ℕ) : Set Plane :=
  {u | a.1 ≤ u.1 ∧ u.1 < a.1 + m ∧ a.2 ≤ u.2 ∧ u.2 < a.2 + m}

theorem square_mono {a : Plane} {m m' : ℕ} (h : m ≤ m') : square a m ⊆ square a m' := by
  intro u hu
  simp only [square, Set.mem_setOf_eq] at hu ⊢
  omega

theorem mem_box_iff {r : ℕ} {u : Plane} :
    u ∈ box r ↔ -(r : ℤ) ≤ u.1 ∧ u.1 ≤ r ∧ -(r : ℤ) ≤ u.2 ∧ u.2 ≤ r := by
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  tauto

theorem box_mono {r r' : ℕ} (h : r ≤ r') : (box r : Set Plane) ⊆ box r' := by
  intro u hu
  rw [Finset.mem_coe, mem_box_iff] at hu ⊢
  omega

/-! ## `set:compact` -/

section Compact

variable {R : WangSet}

/-- `set:compact`, König's lemma in the form used: if every box `V_n` carries a legal pattern of
`R`, then `R` tiles. Proved by compactness of `R^{ℤ²}` (Tychonoff). -/
theorem tiles_of_forall_box (h : ∀ n : ℕ, ∃ p, IsLegalPattern R (box n : Set Plane) p) :
    Tiles R := by
  obtain ⟨p₀, hp₀⟩ := h 0
  have ht₀ : p₀ 0 ∈ R := hp₀.1 0 (by rw [Finset.mem_coe, mem_box_iff]; simp)
  letI : TopologicalSpace R := ⊥
  haveI : DiscreteTopology R := ⟨rfl⟩
  -- the closed sets `C n` of configurations legal on `V_n`
  let C : ℕ → Set (Plane → R) := fun n =>
    {z | LegalOn TileH TileV (box n : Set Plane) (fun u => (z u : Tile))}
  have hclosed_rel : ∀ (u v : Plane) (rel : Tile → Tile → Prop),
      IsClosed {z : Plane → R | rel (z u : Tile) (z v : Tile)} := by
    intro u v rel
    have hc : Continuous fun z : Plane → R => (z u, z v) :=
      (continuous_apply u).prodMk (continuous_apply v)
    exact (isClosed_discrete {q : R × R | rel (q.1 : Tile) (q.2 : Tile)}).preimage hc
  have hclosed : ∀ n, IsClosed (C n) := by
    intro n
    have e : C n = (⋂ u, ⋂ (_ : u ∈ (box n : Set Plane)), ⋂ (_ : u + (1, 0) ∈ (box n : Set Plane)),
        {z : Plane → R | TileH (z u : Tile) (z (u + (1, 0)) : Tile)}) ∩
        (⋂ u, ⋂ (_ : u ∈ (box n : Set Plane)), ⋂ (_ : u + (0, 1) ∈ (box n : Set Plane)),
        {z : Plane → R | TileV (z u : Tile) (z (u + (0, 1)) : Tile)}) := by
      ext z; simp [C, LegalOn]
    rw [e]
    exact (isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      hclosed_rel _ _ _).inter (isClosed_iInter fun u => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => hclosed_rel _ _ _)
  have hne : ∀ n, (C n).Nonempty := by
    intro n
    obtain ⟨p, hpR, hp⟩ := h n
    classical
    refine ⟨fun u => if hu : p u ∈ R then ⟨p u, hu⟩ else ⟨p₀ 0, ht₀⟩, ?_⟩
    refine hp.congr fun u hu => ?_
    simp [hpR u hu]
  have hdec : ∀ n, C (n + 1) ⊆ C n := fun n _ hz =>
    LegalOn.mono (show LegalOn TileH TileV _ _ from hz) (box_mono (Nat.le_succ n))
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hdec hne
    (hclosed 0).isCompact hclosed
  rw [Set.mem_iInter] at hz
  refine ⟨fun u => (z u : Tile), fun u => (z u).2, fun u => ?_, fun u => ?_⟩
  · obtain ⟨r, hr⟩ := ((TokenGame.eventually_mem_box u).and (TokenGame.eventually_mem_box (u + (1, 0)))).exists
    exact (hz r).1 u hr.1 hr.2
  · obtain ⟨r, hr⟩ := ((TokenGame.eventually_mem_box u).and (TokenGame.eventually_mem_box (u + (0, 1)))).exists
    exact (hz r).2 u hr.1 hr.2

/-- A legal pattern on a square of side at least `2n + 1` gives one on the box `V_n`. -/
theorem exists_box_of_square {n m : ℕ} (hm : 2 * n + 1 ≤ m) {a : Plane} {p : Plane → Tile}
    (hp : IsLegalPattern R (square a m) p) : ∃ q, IsLegalPattern R (box n : Set Plane) q := by
  refine ⟨_, (hp.translate (a.1 + n, a.2 + n)).mono ?_⟩
  intro u hu
  rw [Finset.mem_coe, mem_box_iff] at hu
  simp only [square, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add]
  omega

/-- `set:compact`, square form: if squares of every side carry legal patterns, `R` tiles. -/
theorem tiles_of_forall_square (h : ∀ m : ℕ, ∃ a p, IsLegalPattern R (square a m) p) :
    Tiles R :=
  tiles_of_forall_box fun n => by
    obtain ⟨a, p, hp⟩ := h (2 * n + 1)
    exact exists_box_of_square le_rfl hp

/-- **`set:compact`** (as printed). If `R` does not tile, then there is `n ≥ 1` such that no legal
pattern on `V_n` exists, and for such `n` no square of side at least `2n + 1` carries a legal
pattern. -/
theorem compact (hR : ¬ Tiles R) :
    ∃ n ≥ 1, (¬ ∃ p, IsLegalPattern R (box n : Set Plane) p) ∧
      ∀ (a : Plane) (m : ℕ), 2 * n + 1 ≤ m → ¬ ∃ p, IsLegalPattern R (square a m) p := by
  have h0 : ∃ n₀, ¬ ∃ p, IsLegalPattern R (box n₀ : Set Plane) p := by
    by_contra hcon
    push Not at hcon
    exact hR (tiles_of_forall_box hcon)
  obtain ⟨n₀, hn₀⟩ := h0
  have hmono : ∀ n, n₀ ≤ n → ¬ ∃ p, IsLegalPattern R (box n : Set Plane) p :=
    fun n hn ⟨p, hp⟩ => hn₀ ⟨p, hp.mono (box_mono hn)⟩
  refine ⟨max n₀ 1, le_max_right _ _, hmono _ (le_max_left _ _), fun a m hm ⟨p, hp⟩ => ?_⟩
  exact hmono _ (le_max_left _ _) (exists_box_of_square hm hp)

end Compact

end FNE
