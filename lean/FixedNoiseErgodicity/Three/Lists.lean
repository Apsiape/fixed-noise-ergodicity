/-
# §9.2–9.3: list families on the scaffold, the thin phase, the corner grid, `thr:zero`,
# and `thr:corner-plane`

All statements concern list families on `𝔸` alone (no tokens), as in the paper.
* `thr:def-lists`: list families (`IsListFamily`: nonempty lists of letters of `𝔸`) and arc
  consistency (`ArcConsistent`); the fit relation `Letter.Fits` is `Scaffold/Format.lean`'s.
* The thin phase (09:97): `HasThinPhase L c` (the type at `z` is `thinRule (z - c)`).
* **`thr:thin`** (`thr_thin`), the corner sets `𝓛^∠(z)` (`angle`), **`thr:ne`** (`thr_ne_e1`,
  `thr_ne_e2`, `thr_ne_singleton`), **`thr:zero`** (`thr_zero`).
* **`thr:corner-plane`** (`corner_plane`): from the corner lemma on `V_6` (`Three/Corner.lean`);
  **[choice]** proved with `z₀ + V_6` (stronger than the printed `z₀ + V_16`, which follows,
  `corner_plane_V16`).
-/
import FixedNoiseErgodicity.Three.Corner

set_option autoImplicit false

namespace FNE.Three

open FNE.Scaffold

/-! ## List families (`thr:def-lists`) -/

/-- `thr:def-lists`: a *list family* assigns to every `z ∈ ℤ²` a nonempty set `𝓛(z) ⊆ 𝔸`. -/
structure IsListFamily (L : Plane → Set Letter) : Prop where
  nonempty : ∀ z, (L z).Nonempty
  inA : ∀ z, ∀ x ∈ L z, x.InA

/-- `thr:def-lists`: `𝓛` is *arc consistent* if for every `z`, every `𝔞 ∈ 𝓛(z)` and every
direction `e`, some `𝔟 ∈ 𝓛(z + e)` fits `𝔞` in direction `e`. -/
def ArcConsistent (L : Plane → Set Letter) : Prop :=
  ∀ z, ∀ a ∈ L z, ∀ d : Dir, ∃ b ∈ L (z + d.vec), a.Fits d b

/-- 09:97: `𝓛` has *thin phase* `c` if every letter of `𝓛(z)` has thin type `a, c, d, b`
according as `z - c ≡ (0,0), (1,0), (0,1), (1,1) (mod 2)`. -/
def HasThinPhase (L : Plane → Set Letter) (c : Plane) : Prop :=
  ∀ z, ∀ x ∈ L z, x.base.thin = thinRule (z - c)

/-! ## Fitting letters and thin types -/

/-- The thin map of a direction: `↔` for `±e₁`, `↕` for `±e₂`. -/
def _root_.FNE.Scaffold.Dir.thin : Dir → Thin → Thin
  | .e1 => Thin.horiz | .e1' => Thin.horiz | .e2 => Thin.vert | .e2' => Thin.vert

theorem _root_.FNE.Scaffold.Dir.thin_thin (d : Dir) (θ : Thin) : d.thin (d.thin θ) = θ := by
  cases d <;> cases θ <;> rfl

theorem _root_.FNE.Scaffold.Dir.thin_injective (d : Dir) : Function.Injective d.thin :=
  fun θ θ' h => by rw [← d.thin_thin θ, h, d.thin_thin]

theorem fits_e1 {a b : Letter} : a.Fits .e1 b ↔ a.MatchE b := Letter.fits_iff .e1 a b

theorem fits_e1' {a b : Letter} : a.Fits .e1' b ↔ b.MatchE a := Letter.fits_iff .e1' a b

theorem fits_e2 {a b : Letter} : a.Fits .e2 b ↔ a.MatchN b := Letter.fits_iff .e2 a b

theorem fits_e2' {a b : Letter} : a.Fits .e2' b ↔ b.MatchN a := Letter.fits_iff .e2' a b

/-- The components of horizontal matching used below. -/
theorem matchE_parts {x y : Letter} (h : x.MatchE y) :
    x.base.thin.epE = y.base.thin.epW ∧ x.base.thick.epE = y.base.thick.epW ∧
      x.base.black.bitE = y.base.black.bitW ∧ x.b2 = y.b2 := by
  obtain ⟨h1, h2⟩ := Letter.matchE_iff.1 h
  exact ⟨(Formal.matchE_iff.1 h1).1, (Formal.matchE_iff.1 h1).2.1, (Formal.matchE_iff.1 h1).2.2, h2⟩

/-- The components of vertical matching used below. -/
theorem matchN_parts {x y : Letter} (h : x.MatchN y) :
    x.base.thin.epN = y.base.thin.epS ∧ x.base.thick.epN = y.base.thick.epS ∧
      x.base.black.bitN = y.base.black.bitS ∧ x.b1 = y.b1 := by
  obtain ⟨h1, h2⟩ := Letter.matchN_iff.1 h
  exact ⟨(Formal.matchN_iff.1 h1).1, (Formal.matchN_iff.1 h1).2.1, (Formal.matchN_iff.1 h1).2.2, h2⟩

/-- 09:86: along a fit in direction `e`, the thin type changes by `↔` (horizontal) or `↕`
(vertical). -/
theorem _root_.FNE.Scaffold.Letter.Fits.thin {d : Dir} {a b : Letter} (h : a.Fits d b) :
    b.base.thin = d.thin a.base.thin := by
  cases d
  · exact (Thin.epE_eq_epW_iff _ _).1 (matchE_parts (fits_e1.1 h)).1
  · have := (Thin.epE_eq_epW_iff _ _).1 (matchE_parts (fits_e1'.1 h)).1
    rw [this, Dir.thin, Thin.horiz_horiz]
  · exact (Thin.epN_eq_epS_iff _ _).1 (matchN_parts (fits_e2.1 h)).1
  · have := (Thin.epN_eq_epS_iff _ _).1 (matchN_parts (fits_e2'.1 h)).1
    rw [this, Dir.thin, Thin.vert_vert]

/-! ## The thin-type rule -/

theorem thinRule_add (v : Plane) (d : Dir) : thinRule (v + d.vec) = d.thin (thinRule v) := by
  obtain ⟨v1, v2⟩ := v
  have e1 : (v1 + 1) % 2 = 0 ↔ ¬ v1 % 2 = 0 := by omega
  have e2 : (v1 + -1) % 2 = 0 ↔ ¬ v1 % 2 = 0 := by omega
  have e3 : (v2 + 1) % 2 = 0 ↔ ¬ v2 % 2 = 0 := by omega
  have e4 : (v2 + -1) % 2 = 0 ↔ ¬ v2 % 2 = 0 := by omega
  cases d <;> simp only [thinRule, Dir.vec, Prod.mk_add_mk, add_zero, e1, e2, e3, e4] <;>
    by_cases h1 : v1 % 2 = 0 <;> by_cases h2 : v2 % 2 = 0 <;> simp [h1, h2, Dir.thin, Thin.horiz, Thin.vert]

theorem thinRule_add_two_smul (v w : Plane) : thinRule (v + 2 • w) = thinRule v := by
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  have e1 : (v1 + 2 * w1) % 2 = 0 ↔ v1 % 2 = 0 := by omega
  have e2 : (v2 + 2 * w2) % 2 = 0 ↔ v2 % 2 = 0 := by omega
  simp only [thinRule, Prod.smul_mk, nsmul_eq_mul, Nat.cast_ofNat, Prod.mk_add_mk, e1, e2]

theorem thinRule_zero : thinRule 0 = .a := rfl

theorem thinRule_e1 : thinRule (1, 0) = .c := rfl

theorem thinRule_e2 : thinRule (0, 1) = .d := rfl

theorem thinRule_e12 : thinRule (1, 1) = .b := rfl

theorem thinRule_e1' : thinRule (-1, 0) = .c := rfl

theorem thinRule_e2' : thinRule (0, -1) = .d := rfl

/-! ## Induction over the plane -/

/-- A property that passes from every neighbour `z + e` to `z` and holds at `z₀` holds
everywhere. -/
theorem plane_induction {P : Plane → Prop} (z0 : Plane) (h0 : P z0)
    (h : ∀ z, ∀ d : Dir, P (z + d.vec) → P z) (z : Plane) : P z := by
  have key : ∀ a b : ℤ, P (z0 + (a, b)) := by
    have hrow : ∀ a : ℤ, P (z0 + (a, 0)) := by
      intro a
      induction a using Int.induction_on with
      | zero => convert h0 using 1; ext <;> simp
      | succ i ih =>
        refine h _ .e1' ?_
        convert ih using 1
        ext <;> simp [Dir.vec] <;> ring
      | pred i ih =>
        refine h _ .e1 ?_
        convert ih using 1
        ext <;> simp [Dir.vec] <;> ring
    intro a b
    induction b using Int.induction_on with
    | zero => exact hrow a
    | succ i ih =>
      refine h _ .e2' ?_
      convert ih using 1
      ext <;> simp [Dir.vec] <;> ring
    | pred i ih =>
      refine h _ .e2 ?_
      convert ih using 1
      ext <;> simp [Dir.vec] <;> ring
  have := key (z - z0).1 (z - z0).2
  convert this using 1
  ext <;> simp

/-! ## `thr:thin` -/

/-- The propagation step of `thr:thin`: if the rule holds at `z₀`, it holds everywhere. -/
theorem hasThinPhase_of {L : Plane → Set Letter} (hac : ArcConsistent L) (c z0 : Plane)
    (h0 : ∀ x ∈ L z0, x.base.thin = thinRule (z0 - c)) : HasThinPhase L c := by
  refine plane_induction (P := fun z => ∀ x ∈ L z, x.base.thin = thinRule (z - c)) z0 h0 ?_
  intro z d hz x hx
  obtain ⟨y, hy, hfit⟩ := hac z x hx d
  have h1 := hfit.thin
  rw [hz y hy, show z + d.vec - c = z - c + d.vec by abel, thinRule_add] at h1
  exact d.thin_injective h1.symm

/-- **`thr:thin`.** If `𝓛` is arc consistent and all letters of `𝓛(z₀)` have one thin type
`θ₀`, then `𝓛` has a thin phase, which assigns `θ₀` to `z₀`. -/
theorem thr_thin {L : Plane → Set Letter} (hac : ArcConsistent L) {z0 : Plane} {θ0 : Thin}
    (h0 : ∀ x ∈ L z0, x.base.thin = θ0) : ∃ c, HasThinPhase L c ∧ thinRule (z0 - c) = θ0 := by
  obtain ⟨w, hw⟩ : ∃ w : Plane, thinRule w = θ0 := by
    cases θ0
    exacts [⟨(0, 0), rfl⟩, ⟨(1, 1), rfl⟩, ⟨(1, 0), rfl⟩, ⟨(0, 1), rfl⟩]
  refine ⟨z0 - w, hasThinPhase_of hac _ z0 ?_, ?_⟩ <;> rw [sub_sub_cancel] <;> [exact hw ▸ h0; exact hw]

/-- `thr:thin` for a list with thin type `a` at `z₀`: thin phase `z₀`. -/
theorem hasThinPhase_self {L : Plane → Set Letter} (hac : ArcConsistent L) {z0 : Plane}
    (h0 : ∀ x ∈ L z0, x.base.thin = .a) : HasThinPhase L z0 :=
  hasThinPhase_of hac z0 z0 (by rw [sub_self]; exact h0)

/-! ## The corner grid (`thr:ne`) -/

/-- 09:88: the letter `(b, F(θ), A, 0, 0)`. -/
def bLetter (θ : Thin) : Letter := ⟨⟨.b, .corner (F θ), .A⟩, false, false⟩

/-- 09:107: the north-east site of `z` for thin phase `c` is `c + 2z + (1,1)`, and `𝓛^∠(z)` is the
set of `θ` with `(b, F(θ), A, 0, 0) ∈ 𝓛(c + 2z + (1,1))`. -/
def angle (L : Plane → Set Letter) (c z : Plane) : Set Thin := {θ | bLetter θ ∈ L (c + 2 • z + (1, 1))}

section Grid

variable {L : Plane → Set Letter} {c : Plane}

theorem thin_at (hc : HasThinPhase L c) {z w : Plane} {x : Letter} (hx : x ∈ L (c + 2 • z + w)) :
    x.base.thin = thinRule w := by
  rw [hc _ x hx, show c + 2 • z + w - c = w + 2 • z by abel, thinRule_add_two_smul]

/-- 09:107: every letter at the north-east site is `bLetter θ` with `θ ∈ 𝓛^∠(z)`. -/
theorem eq_bLetter (hL : IsListFamily L) (hc : HasThinPhase L c) {z : Plane} {x : Letter}
    (hx : x ∈ L (c + 2 • z + (1, 1))) : ∃ θ ∈ angle L c z, x = bLetter θ := by
  obtain ⟨θ, rfl⟩ := (hL.inA _ x hx).thin_b (thin_at hc hx)
  exact ⟨θ, hx, rfl⟩

theorem angle_nonempty (hL : IsListFamily L) (hc : HasThinPhase L c) (z : Plane) :
    (angle L c z).Nonempty := by
  obtain ⟨x, hx⟩ := hL.nonempty (c + 2 • z + (1, 1))
  obtain ⟨θ, hθ, -⟩ := eq_bLetter hL hc hx
  exact ⟨θ, hθ⟩

theorem thick_epE_eq_epW {κ : Thick} (h : ¬ κ.IsCorner) : κ.epE = κ.epW := by
  cases κ with
  | corner _ => exact (h trivial).elim
  | line _ _ => rfl

theorem thick_epN_eq_epS {κ : Thick} (h : ¬ κ.IsCorner) : κ.epN = κ.epS := by
  cases κ with
  | corner _ => exact (h trivial).elim
  | line _ _ => rfl

/-- The horizontal step of `thr:ne`: `θ^↔ ∈ 𝓛^∠(z + e₁)` for `θ ∈ 𝓛^∠(z)`, and conversely. -/
theorem angle_e1_of (hL : IsListFamily L) (hac : ArcConsistent L) (hc : HasThinPhase L c)
    {z : Plane} {θ : Thin} (hθ : θ ∈ angle L c z) : θ.horiz ∈ angle L c (z + (1, 0)) := by
  obtain ⟨l, hl, h1⟩ := hac _ _ hθ .e1
  obtain ⟨n', hn', h2⟩ := hac _ _ hl .e1
  have e1 : c + 2 • z + (1, 1) + Dir.vec .e1 = c + 2 • (z + (1, 0)) + (0, 1) := by
    simp only [Dir.vec]; ext <;> simp <;> ring
  have e2 : c + 2 • z + (1, 1) + Dir.vec .e1 + Dir.vec .e1 = c + 2 • (z + (1, 0)) + (1, 1) := by
    simp only [Dir.vec]; ext <;> simp <;> ring
  rw [e1] at hl
  rw [e2] at hn'
  have hlA := hL.inA _ l hl
  have hld := (T3_d hlA (thin_at hc hl)).1
  obtain ⟨θ', hθ', rfl⟩ := eq_bLetter hL hc hn'
  have k1 := (matchE_parts (fits_e1.1 h1)).2.1
  have k2 := (matchE_parts (fits_e1.1 h2)).2.1
  rw [← thick_epE_eq_epW hld] at k1
  have : (F θ).epE = (F θ').epW := k1.trans k2
  rw [Thin.F_epE_eq_F_epW_iff] at this
  rwa [← this]

theorem angle_e1_of' (hL : IsListFamily L) (hac : ArcConsistent L) (hc : HasThinPhase L c)
    {z : Plane} {θ' : Thin} (hθ' : θ' ∈ angle L c (z + (1, 0))) : θ'.horiz ∈ angle L c z := by
  obtain ⟨l, hl, h1⟩ := hac _ _ hθ' .e1'
  obtain ⟨n, hn, h2⟩ := hac _ _ hl .e1'
  have e1 : c + 2 • (z + (1, 0)) + (1, 1) + Dir.vec .e1' = c + 2 • (z + (1, 0)) + (0, 1) := by
    simp only [Dir.vec]; ext <;> simp
  have e2 : c + 2 • (z + (1, 0)) + (1, 1) + Dir.vec .e1' + Dir.vec .e1' = c + 2 • z + (1, 1) := by
    simp only [Dir.vec]; ext <;> simp <;> ring
  rw [e1] at hl
  rw [e2] at hn
  have hlA := hL.inA _ l hl
  have hld := (T3_d hlA (thin_at hc hl)).1
  obtain ⟨θ, hθ, rfl⟩ := eq_bLetter hL hc hn
  have k1 := (matchE_parts (fits_e1'.1 h1)).2.1
  have k2 := (matchE_parts (fits_e1'.1 h2)).2.1
  rw [thick_epE_eq_epW hld] at k1
  have : (F θ).epE = (F θ').epW := k2.trans k1
  rw [Thin.F_epE_eq_F_epW_iff] at this
  rwa [this, Thin.horiz_horiz]

/-- The vertical step of `thr:ne`. -/
theorem angle_e2_of (hL : IsListFamily L) (hac : ArcConsistent L) (hc : HasThinPhase L c)
    {z : Plane} {θ : Thin} (hθ : θ ∈ angle L c z) : θ.vert ∈ angle L c (z + (0, 1)) := by
  obtain ⟨l, hl, h1⟩ := hac _ _ hθ .e2
  obtain ⟨n', hn', h2⟩ := hac _ _ hl .e2
  have e1 : c + 2 • z + (1, 1) + Dir.vec .e2 = c + 2 • (z + (0, 1)) + (1, 0) := by
    simp only [Dir.vec]; ext <;> simp <;> ring
  have e2 : c + 2 • z + (1, 1) + Dir.vec .e2 + Dir.vec .e2 = c + 2 • (z + (0, 1)) + (1, 1) := by
    simp only [Dir.vec]; ext <;> simp <;> ring
  rw [e1] at hl
  rw [e2] at hn'
  have hlA := hL.inA _ l hl
  have hlc := (T3_c hlA (thin_at hc hl)).1
  obtain ⟨θ', hθ', rfl⟩ := eq_bLetter hL hc hn'
  have k1 := (matchN_parts (fits_e2.1 h1)).2.1
  have k2 := (matchN_parts (fits_e2.1 h2)).2.1
  rw [← thick_epN_eq_epS hlc] at k1
  have : (F θ).epN = (F θ').epS := k1.trans k2
  rw [Thin.F_epN_eq_F_epS_iff] at this
  rwa [← this]

theorem angle_e2_of' (hL : IsListFamily L) (hac : ArcConsistent L) (hc : HasThinPhase L c)
    {z : Plane} {θ' : Thin} (hθ' : θ' ∈ angle L c (z + (0, 1))) : θ'.vert ∈ angle L c z := by
  obtain ⟨l, hl, h1⟩ := hac _ _ hθ' .e2'
  obtain ⟨n, hn, h2⟩ := hac _ _ hl .e2'
  have e1 : c + 2 • (z + (0, 1)) + (1, 1) + Dir.vec .e2' = c + 2 • (z + (0, 1)) + (1, 0) := by
    simp only [Dir.vec]; ext <;> simp
  have e2 : c + 2 • (z + (0, 1)) + (1, 1) + Dir.vec .e2' + Dir.vec .e2' = c + 2 • z + (1, 1) := by
    simp only [Dir.vec]; ext <;> simp <;> ring
  rw [e1] at hl
  rw [e2] at hn
  have hlA := hL.inA _ l hl
  have hlc := (T3_c hlA (thin_at hc hl)).1
  obtain ⟨θ, hθ, rfl⟩ := eq_bLetter hL hc hn
  have k1 := (matchN_parts (fits_e2'.1 h1)).2.1
  have k2 := (matchN_parts (fits_e2'.1 h2)).2.1
  rw [thick_epN_eq_epS hlc] at k1
  have : (F θ).epN = (F θ').epS := k2.trans k1
  rw [Thin.F_epN_eq_F_epS_iff] at this
  rwa [this, Thin.vert_vert]

theorem image_horiz_horiz (s : Set Thin) : Thin.horiz '' (Thin.horiz '' s) = s := by
  rw [Set.image_image]; simp [Thin.horiz_horiz]

theorem image_vert_vert (s : Set Thin) : Thin.vert '' (Thin.vert '' s) = s := by
  rw [Set.image_image]; simp [Thin.vert_vert]

/-- **`thr:ne`**, first claim, horizontal: `𝓛^∠(z + e₁) = {θ^↔ : θ ∈ 𝓛^∠(z)}`. -/
theorem thr_ne_e1 (hL : IsListFamily L) (hac : ArcConsistent L) (hc : HasThinPhase L c)
    (z : Plane) : angle L c (z + (1, 0)) = Thin.horiz '' angle L c z := by
  ext θ'
  refine ⟨fun h => ⟨θ'.horiz, angle_e1_of' hL hac hc h, Thin.horiz_horiz θ'⟩, ?_⟩
  rintro ⟨θ, hθ, rfl⟩
  exact angle_e1_of hL hac hc hθ

/-- **`thr:ne`**, first claim, vertical: `𝓛^∠(z + e₂) = {θ^↕ : θ ∈ 𝓛^∠(z)}`. -/
theorem thr_ne_e2 (hL : IsListFamily L) (hac : ArcConsistent L) (hc : HasThinPhase L c)
    (z : Plane) : angle L c (z + (0, 1)) = Thin.vert '' angle L c z := by
  ext θ'
  refine ⟨fun h => ⟨θ'.vert, angle_e2_of' hL hac hc h, Thin.vert_vert θ'⟩, ?_⟩
  rintro ⟨θ, hθ, rfl⟩
  exact angle_e2_of hL hac hc hθ

/-- `thr:ne` along any direction: `𝓛^∠(z) = d.thin '' 𝓛^∠(z + e)`. -/
theorem angle_eq_image (hL : IsListFamily L) (hac : ArcConsistent L) (hc : HasThinPhase L c)
    (z : Plane) (d : Dir) : angle L c z = d.thin '' angle L c (z + d.vec) := by
  cases d
  · rw [Dir.vec, thr_ne_e1 hL hac hc, Dir.thin, image_horiz_horiz]
  · have := thr_ne_e1 hL hac hc (z + (-1, 0))
    rw [show z + (-1, 0) + (1, 0) = z by ext <;> simp] at this
    rw [Dir.vec, this, Dir.thin]
  · rw [Dir.vec, thr_ne_e2 hL hac hc, Dir.thin, image_vert_vert]
  · have := thr_ne_e2 hL hac hc (z + (0, -1))
    rw [show z + (0, -1) + (0, 1) = z by ext <;> simp] at this
    rw [Dir.vec, this, Dir.thin]

/-- If `𝓛^∠(z₀) = {θ₀}`, then `𝓛^∠(z) = {ρ(z)}` for every map `ρ` with `ρ(z₀) = θ₀` that follows
the rule of the thin maps. -/
theorem angle_eq_of_rule (hL : IsListFamily L) (hac : ArcConsistent L) (hc : HasThinPhase L c)
    {z0 : Plane} {ρ : Plane → Thin} (h0 : angle L c z0 = {ρ z0})
    (hρ : ∀ (z : Plane) (d : Dir), ρ z = d.thin (ρ (z + d.vec))) (z : Plane) : angle L c z = {ρ z} := by
  refine plane_induction (P := fun z => angle L c z = {ρ z}) z0 h0 ?_ z
  intro z d hz
  rw [angle_eq_image hL hac hc z d, hz, Set.image_singleton, ← hρ]

/-- **`thr:ne`**, second claim: if `𝓛^∠(z₀)` is a singleton, then every `𝓛^∠(z)` is a singleton
`{θ_z}`, with `θ_{z+e₁} = θ_z^↔` and `θ_{z+e₂} = θ_z^↕`. -/
theorem thr_ne_singleton (hL : IsListFamily L) (hac : ArcConsistent L) (hc : HasThinPhase L c)
    {z0 : Plane} {θ0 : Thin} (h0 : angle L c z0 = {θ0}) :
    ∃ θ : Plane → Thin, ∀ z, angle L c z = {θ z} ∧ θ (z + (1, 0)) = (θ z).horiz ∧
      θ (z + (0, 1)) = (θ z).vert := by
  have hs : ∀ z, ∃ θ, angle L c z = {θ} := by
    refine plane_induction (P := fun z => ∃ θ, angle L c z = {θ}) z0 ⟨θ0, h0⟩ ?_
    rintro z d ⟨θ, hθ⟩
    exact ⟨d.thin θ, by rw [angle_eq_image hL hac hc z d, hθ, Set.image_singleton]⟩
  choose θ hθ using hs
  refine ⟨θ, fun z => ⟨hθ z, ?_, ?_⟩⟩
  · have := thr_ne_e1 hL hac hc z
    rw [hθ, hθ, Set.image_singleton, Set.singleton_eq_singleton_iff] at this
    exact this
  · have := thr_ne_e2 hL hac hc z
    rw [hθ, hθ, Set.image_singleton, Set.singleton_eq_singleton_iff] at this
    exact this

end Grid

/-! ## `thr:zero` -/

section Zero

variable {L : Plane → Set Letter} {c : Plane}

/-- The `(T2)` condition `∂_W θ` green is invariant under `↕`, and `∂_S θ` green under `↔`. -/
theorem epW_red_vert (θ : Thin) : θ.vert.epW.IsRed ↔ θ.epW.IsRed := by cases θ <;> decide

theorem epS_red_horiz (θ : Thin) : θ.horiz.epS.IsRed ↔ θ.epS.IsRed := by cases θ <;> decide

theorem eq_a_of_green (θ : Thin) (h1 : ¬ θ.epW.IsRed) (h2 : ¬ θ.epS.IsRed) : θ = .a := by
  cases θ <;> simp_all [Thin.epW, Thin.epS, HAtom.IsRed, VAtom.IsRed]

theorem T4' {l : Letter} (hl : l.InA) (hnc : ¬ l.base.thick.IsCorner) (hb : l.b1 = l.b2)
    (h : l.base.thick.epN.IsRed) : ¬ l.base.thick.epE.IsRed := by
  obtain ⟨⟨θ, κ, ω⟩, b1, b2⟩ := l
  cases κ with
  | corner _ => exact (hnc trivial).elim
  | line α γ => exact fun h' => T4 hl rfl hb ⟨h, h'⟩

/-- `thr:zero`, north case: if `∂_N κ` is red, every `θ ∈ 𝓛^∠(z₀)` has `∂_W θ` green. -/
theorem zero_N (hL : IsListFamily L) (hac : ArcConsistent L) (hc : HasThinPhase L c)
    {z0 : Plane} {κ : Corner} (hp : L (c + 2 • z0) = {cornerLetter κ false})
    (hN : κ.epN.IsRed) {θ : Thin} (hθ : θ ∈ angle L c z0) : ¬ θ.epW.IsRed := by
  obtain ⟨l, hl, h1⟩ := hac _ _ hθ .e1'
  have e1 : c + 2 • z0 + (1, 1) + Dir.vec .e1' = c + 2 • z0 + (0, 1) := by
    simp only [Dir.vec]; ext <;> simp
  rw [e1] at hl
  obtain ⟨p, hp', h2⟩ := hac _ _ hl .e2'
  have e2 : c + 2 • z0 + (0, 1) + Dir.vec .e2' = c + 2 • z0 := by
    simp only [Dir.vec]; ext <;> simp
  rw [e2, hp, Set.mem_singleton_iff] at hp'
  subst hp'
  have hlA := hL.inA _ l hl
  obtain ⟨hnc, -, hb2, -⟩ := T3_d hlA (thin_at hc hl)
  have m1 := matchE_parts (fits_e1'.1 h1)
  have m2 := matchN_parts (fits_e2'.1 h2)
  have hb : l.b1 = l.b2 := by rw [hb2, ← m2.2.2.2]; rfl
  have hred : l.base.thick.epN.IsRed := by
    rw [thick_epN_eq_epS hnc, ← m2.2.1]; exact hN
  have := T4' hlA hnc hb hred
  rwa [m1.2.1, show (bLetter θ).base.thick.epW = θ.epW from F_epW θ] at this

/-- `thr:zero`, south case: if `∂_S κ` is red, every `θ ∈ 𝓛^∠(z₀ - e₂)` has `∂_W θ` green. -/
theorem zero_S (hL : IsListFamily L) (hac : ArcConsistent L) (hc : HasThinPhase L c)
    {z0 : Plane} {κ : Corner} (hp : L (c + 2 • z0) = {cornerLetter κ false})
    (hS : κ.epS.IsRed) {θ : Thin} (hθ : θ ∈ angle L c (z0 + (0, -1))) : ¬ θ.epW.IsRed := by
  obtain ⟨l, hl, h1⟩ := hac _ _ hθ .e1'
  have e1 : c + 2 • (z0 + (0, -1)) + (1, 1) + Dir.vec .e1' = c + 2 • z0 + (0, -1) := by
    simp only [Dir.vec]; ext <;> simp <;> ring
  rw [e1] at hl
  obtain ⟨p, hp', h2⟩ := hac _ _ hl .e2
  have e2 : c + 2 • z0 + (0, -1) + Dir.vec .e2 = c + 2 • z0 := by
    simp only [Dir.vec]; ext <;> simp
  rw [e2, hp, Set.mem_singleton_iff] at hp'
  subst hp'
  have hlA := hL.inA _ l hl
  obtain ⟨hnc, -, hb2, -⟩ := T3_d hlA (by rw [thin_at hc hl]; rfl)
  have m1 := matchE_parts (fits_e1'.1 h1)
  have m2 := matchN_parts (fits_e2.1 h2)
  have hb : l.b1 = l.b2 := by rw [hb2, m2.2.2.2]; rfl
  have hred : l.base.thick.epN.IsRed := by rw [m2.2.1]; exact hS
  have := T4' hlA hnc hb hred
  rwa [m1.2.1, show (bLetter θ).base.thick.epW = θ.epW from F_epW θ] at this

/-- `thr:zero`, east case: if `∂_E κ` is red, every `θ ∈ 𝓛^∠(z₀)` has `∂_S θ` green. -/
theorem zero_E (hL : IsListFamily L) (hac : ArcConsistent L) (hc : HasThinPhase L c)
    {z0 : Plane} {κ : Corner} (hp : L (c + 2 • z0) = {cornerLetter κ false})
    (hE : κ.epE.IsRed) {θ : Thin} (hθ : θ ∈ angle L c z0) : ¬ θ.epS.IsRed := by
  obtain ⟨l, hl, h1⟩ := hac _ _ hθ .e2'
  have e1 : c + 2 • z0 + (1, 1) + Dir.vec .e2' = c + 2 • z0 + (1, 0) := by
    simp only [Dir.vec]; ext <;> simp
  rw [e1] at hl
  obtain ⟨p, hp', h2⟩ := hac _ _ hl .e1'
  have e2 : c + 2 • z0 + (1, 0) + Dir.vec .e1' = c + 2 • z0 := by
    simp only [Dir.vec]; ext <;> simp
  rw [e2, hp, Set.mem_singleton_iff] at hp'
  subst hp'
  have hlA := hL.inA _ l hl
  obtain ⟨hnc, -, hb1, -⟩ := T3_c hlA (thin_at hc hl)
  have m1 := matchN_parts (fits_e2'.1 h1)
  have m2 := matchE_parts (fits_e1'.1 h2)
  have hb : l.b1 = l.b2 := by rw [hb1, ← m2.2.2.2]; rfl
  have hred : l.base.thick.epE.IsRed := by
    rw [thick_epE_eq_epW hnc, ← m2.2.1]; exact hE
  have h3 : ¬ l.base.thick.epN.IsRed := fun h => T4' hlA hnc hb h hred
  rwa [m1.2.1, show (bLetter θ).base.thick.epS = θ.epS from F_epS θ] at h3

/-- `thr:zero`, west case: if `∂_W κ` is red, every `θ ∈ 𝓛^∠(z₀ - e₁)` has `∂_S θ` green. -/
theorem zero_W (hL : IsListFamily L) (hac : ArcConsistent L) (hc : HasThinPhase L c)
    {z0 : Plane} {κ : Corner} (hp : L (c + 2 • z0) = {cornerLetter κ false})
    (hW : κ.epW.IsRed) {θ : Thin} (hθ : θ ∈ angle L c (z0 + (-1, 0))) : ¬ θ.epS.IsRed := by
  obtain ⟨l, hl, h1⟩ := hac _ _ hθ .e2'
  have e1 : c + 2 • (z0 + (-1, 0)) + (1, 1) + Dir.vec .e2' = c + 2 • z0 + (-1, 0) := by
    simp only [Dir.vec]; ext <;> simp <;> ring
  rw [e1] at hl
  obtain ⟨p, hp', h2⟩ := hac _ _ hl .e1
  have e2 : c + 2 • z0 + (-1, 0) + Dir.vec .e1 = c + 2 • z0 := by
    simp only [Dir.vec]; ext <;> simp
  rw [e2, hp, Set.mem_singleton_iff] at hp'
  subst hp'
  have hlA := hL.inA _ l hl
  obtain ⟨hnc, -, hb1, -⟩ := T3_c hlA (by rw [thin_at hc hl]; rfl)
  have m1 := matchN_parts (fits_e2'.1 h1)
  have m2 := matchE_parts (fits_e1.1 h2)
  have hb : l.b1 = l.b2 := by rw [hb1, m2.2.2.2]; rfl
  have hred : l.base.thick.epE.IsRed := by rw [m2.2.1]; exact hW
  have h3 : ¬ l.base.thick.epN.IsRed := fun h => T4' hlA hnc hb h hred
  rwa [m1.2.1, show (bLetter θ).base.thick.epS = θ.epS from F_epS θ] at h3

/-- **`thr:zero`.** Let `𝓛` be arc consistent with thin phase `c`, and let
`𝓛(c + 2z₀) = {𝔭}` for a corner letter `𝔭` with bit `0`. Then every `𝓛^∠(z)` is a singleton
`{θ_z}`, and `θ_z = a` exactly when `z ∈ z₀ + 2ℤ²`; namely `θ_z` is the rule `thinRule (z - z₀)`. -/
theorem thr_zero (hL : IsListFamily L) (hac : ArcConsistent L) (hc : HasThinPhase L c)
    {z0 : Plane} {κ : Corner} (hp : L (c + 2 • z0) = {cornerLetter κ false}) (z : Plane) :
    angle L c z = {thinRule (z - z0)} := by
  have hW : ∀ θ ∈ angle L c z0, ¬ θ.epW.IsRed := by
    intro θ hθ
    by_cases hN : κ.epN.IsRed
    · exact zero_N hL hac hc hp hN hθ
    · have hS : κ.epS.IsRed := by
        by_contra hS; exact hN ((T1 κ).1.2 hS)
      have := angle_eq_image hL hac hc z0 .e2'
      rw [this] at hθ
      obtain ⟨θ', hθ', rfl⟩ := hθ
      rw [Dir.thin, epW_red_vert]
      exact zero_S hL hac hc hp hS hθ'
  have hS : ∀ θ ∈ angle L c z0, ¬ θ.epS.IsRed := by
    intro θ hθ
    by_cases hE : κ.epE.IsRed
    · exact zero_E hL hac hc hp hE hθ
    · have hW' : κ.epW.IsRed := by
        by_contra hW'; exact hE ((T1 κ).2.2 hW')
      have := angle_eq_image hL hac hc z0 .e1'
      rw [this] at hθ
      obtain ⟨θ', hθ', rfl⟩ := hθ
      rw [Dir.thin, epS_red_horiz]
      exact zero_W hL hac hc hp hW' hθ'
  have h0 : angle L c z0 = {thinRule (z0 - z0)} := by
    rw [sub_self, thinRule_zero]
    obtain ⟨θ, hθ⟩ := angle_nonempty hL hc z0
    refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, fun θ' h' => eq_a_of_green θ' (hW θ' h') (hS θ' h')⟩
    rwa [← eq_a_of_green θ (hW θ hθ) (hS θ hθ)]
  refine angle_eq_of_rule hL hac hc (ρ := fun z => thinRule (z - z0)) h0 ?_ z
  intro z d
  rw [show z + d.vec - z0 = z - z0 + d.vec by abel, thinRule_add, Dir.thin_thin]

end Zero

/-! ## `thr:corner-plane` -/

/-- **`thr:corner-plane`.** Let `𝓛` be an arc-consistent list family with
`𝓛(z₀) = {(a, κ, A, 1, 1)}`. Then some `z ∈ z₀ + V_6` has a corner letter with bit `0` in
`𝓛(z)`. **[choice]** `V_6` in place of the printed `V_16` (a strengthening; the corner lemma on
`V_6`, `Three/Corner.lean`). -/
theorem corner_plane {L : Plane → Set Letter} (hL : IsListFamily L) (hac : ArcConsistent L)
    {z0 : Plane} {κ : Corner} (h0 : L z0 = {cornerLetter κ true}) :
    ∃ v ∈ (box 6 : Set Plane), ∃ κ', cornerLetter κ' false ∈ L (z0 + v) := by
  by_contra hno
  push Not at hno
  have hc : HasThinPhase L z0 :=
    hasThinPhase_self hac (by rw [h0]; rintro x rfl; rfl)
  have hK : ConsistentOn (box 6) (fun v => L (z0 + v)) := by
    intro v _ a ha d _
    obtain ⟨b, hb, hfit⟩ := hac _ a ha d
    exact ⟨b, show b ∈ L (z0 + (v + d.vec)) by rwa [← add_assoc], hfit⟩
  have hD : ∀ v ∈ (box 6 : Set Plane), ∀ x ∈ L (z0 + v), InD κ v x := by
    intro v hv x hx
    unfold InD
    split_ifs with hv0
    · subst hv0; rw [add_zero, h0] at hx; exact hx
    · refine ⟨hL.inA _ x hx, ?_, fun κ' h => hno v hv κ' (h ▸ hx)⟩
      rw [hc _ x hx, add_sub_cancel_left]
  have := corner_lemma κ hK hD
  have h1 : cornerLetter κ true ∈ L (z0 + 0) := by rw [add_zero, h0]; rfl
  rw [this] at h1
  exact h1

/-- `thr:corner-plane` as printed, with `z₀ + V_16`. -/
theorem corner_plane_V16 {L : Plane → Set Letter} (hL : IsListFamily L) (hac : ArcConsistent L)
    {z0 : Plane} {κ : Corner} (h0 : L z0 = {cornerLetter κ true}) :
    ∃ v ∈ (box 16 : Set Plane), ∃ κ', cornerLetter κ' false ∈ L (z0 + v) := by
  obtain ⟨v, hv, h⟩ := corner_plane hL hac h0
  exact ⟨v, box_mono (by norm_num) hv, h⟩

end FNE.Three
