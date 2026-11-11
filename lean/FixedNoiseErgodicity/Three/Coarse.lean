/-
# §9.2: coarsening (`thr:coarse`)

Let `𝓛` be an arc-consistent list family with thin phase `c` whose corner sets are singletons,
`𝓛^∠(z) = {θ_z}` (`CoarseSetup`). For `𝔞 = (a, κ, ω, b₁, b₂) ∈ 𝓛(c + 2z)` put
`𝔞↑ = (θ_z, κ, ω, 1 − b₁, 1 − b₂)` (`up`) and `𝓛↑(z) = {𝔞↑ : 𝔞 ∈ 𝓛(c + 2z)}` (`coarsen`).
* `thr:coarse`(a): `up_inA`, `up_inj`;
* `thr:coarse`(b): `coarsen_family`, `coarsen_thin`, `coarsen_ac`, `coarsen_phase`;
* `thr:coarse`(c): `coarsen_singleton` (`𝓛(c + 2z + ς) = {φ'(𝔠)(ς)}`).
The proof follows the paper: (∗) is `se_epN`, `nw_epE`; the four cases of `θ_z` are `b_case`,
`c_case`, `d_case` (with the global step through `z + e₂`, `z + e₁` for the bits).
-/
import FixedNoiseErgodicity.Three.Lists

set_option autoImplicit false

namespace FNE.Three

open FNE.Scaffold

/-- Site arithmetic in `ℤ²`. -/
macro "site_eq" : tactic =>
  `(tactic| (ext <;> simp only [two_nsmul, Prod.fst_add, Prod.snd_add, Dir.vec] <;> ring))

/-! ## Table facts used in the cases `θ_z = b, c, d` -/

theorem inO_b_corner (k : Corner) : (⟨.b, .corner k, .A⟩ : Formal).InO := by
  cases k <;> decide

theorem inO_c_iff {ω : Black} (h : ω = .B ∨ ω = .C) :
    ∀ κ : Thick, (⟨.c, κ, ω⟩ : Formal).InO ↔ (⟨.a, κ, ω⟩ : Formal).InO := by
  rcases h with rfl | rfl <;> decide

theorem inO_d_iff {ω : Black} (h : ω = .D ∨ ω = .E) :
    ∀ κ : Thick, (⟨.d, κ, ω⟩ : Formal).InO ↔ (⟨.a, κ, ω⟩ : Formal).InO := by
  rcases h with rfl | rfl <;> decide

/-- (T3): `B` and `C` have equal east and west bits. -/
theorem bitE_eq_bitW {ω : Black} (h : ω = .B ∨ ω = .C) : ω.bitE = ω.bitW := by
  rcases h with rfl | rfl <;> rfl

/-- (T3): `D` and `E` have equal north and south bits. -/
theorem bitN_eq_bitS {ω : Black} (h : ω = .D ∨ ω = .E) : ω.bitN = ω.bitS := by
  rcases h with rfl | rfl <;> rfl

theorem exists_corner {κ : Thick} (h : κ.IsCorner) : ∃ k, κ = .corner k := by
  cases κ with
  | corner k => exact ⟨k, rfl⟩
  | line _ _ => exact h.elim

theorem exists_line {κ : Thick} (h : ¬ κ.IsCorner) : ∃ α γ, κ = .line α γ := by
  cases κ with
  | corner _ => exact (h trivial).elim
  | line α γ => exact ⟨α, γ, rfl⟩

/-! ## The coarsening map -/

/-- 09:139: `𝔞↑ = (θ, κ, ω, 1 − b₁, 1 − b₂)` for `𝔞 = (a, κ, ω, b₁, b₂)`. -/
def up (θ : Thin) (a : Letter) : Letter := ⟨⟨θ, a.base.thick, a.base.black⟩, !a.b1, !a.b2⟩

/-- 09:139: the coarsening `𝓛↑(z) = {𝔞↑ : 𝔞 ∈ 𝓛(c + 2z)}`, with `θ_z` read from `θ`. -/
def coarsen (L : Plane → Set Letter) (c : Plane) (θ : Plane → Thin) (z : Plane) : Set Letter :=
  up (θ z) '' L (c + 2 • z)

/-- The hypotheses of `thr:coarse`: `𝓛` is an arc-consistent list family with thin phase `c`,
and `𝓛^∠(z) = {θ_z}` for every `z`. -/
structure CoarseSetup (L : Plane → Set Letter) (c : Plane) (θ : Plane → Thin) : Prop where
  fam : IsListFamily L
  ac : ArcConsistent L
  phase : HasThinPhase L c
  angle_eq : ∀ z, angle L c z = {θ z}

namespace CoarseSetup

variable {L : Plane → Set Letter} {c : Plane} {θ : Plane → Thin} (S : CoarseSetup L c θ)
include S

theorem θ_e1 (z : Plane) : θ (z + (1, 0)) = (θ z).horiz := by
  have := thr_ne_e1 S.fam S.ac S.phase z
  rwa [S.angle_eq, S.angle_eq, Set.image_singleton, Set.singleton_eq_singleton_iff] at this

theorem θ_e2 (z : Plane) : θ (z + (0, 1)) = (θ z).vert := by
  have := thr_ne_e2 S.fam S.ac S.phase z
  rwa [S.angle_eq, S.angle_eq, Set.image_singleton, Set.singleton_eq_singleton_iff] at this

theorem θ_e1' (z : Plane) : θ (z + (-1, 0)) = (θ z).horiz := by
  have := S.θ_e1 (z + (-1, 0))
  rw [show z + (-1, 0) + (1, 0) = z by site_eq] at this
  rw [this, Thin.horiz_horiz]

theorem θ_e2' (z : Plane) : θ (z + (0, -1)) = (θ z).vert := by
  have := S.θ_e2 (z + (0, -1))
  rw [show z + (0, -1) + (0, 1) = z by site_eq] at this
  rw [this, Thin.vert_vert]

theorem sw_thin (z : Plane) {a : Letter} (ha : a ∈ L (c + 2 • z)) : a.base.thin = .a := by
  rw [S.phase _ a ha, show c + 2 • z - c = 0 + 2 • z by abel, thinRule_add_two_smul]; rfl

theorem ne_eq (z : Plane) {y : Letter} (hy : y ∈ L (c + 2 • z + (1, 1))) : y = bLetter (θ z) := by
  obtain ⟨θ', hθ', rfl⟩ := eq_bLetter S.fam S.phase hy
  rw [S.angle_eq, Set.mem_singleton_iff] at hθ'
  rw [hθ']

/-- (∗), south-east: every letter at the south-east site of `z` has vertical atom `∂_S θ_z`. -/
theorem se_epN (z : Plane) {l : Letter} (hl : l ∈ L (c + 2 • z + (1, 0))) :
    l.base.thick.epN = (θ z).epS := by
  obtain ⟨n, hn, h⟩ := S.ac _ l hl .e2
  rw [show c + 2 • z + (1, 0) + Dir.vec .e2 = c + 2 • z + (1, 1) by site_eq] at hn
  rw [S.ne_eq z hn] at h
  exact (matchN_parts (fits_e2.1 h)).2.1.trans (F_epS _)

/-- (∗), north-west: every letter at the north-west site of `z` has horizontal atom `∂_W θ_z`. -/
theorem nw_epE (z : Plane) {l : Letter} (hl : l ∈ L (c + 2 • z + (0, 1))) :
    l.base.thick.epE = (θ z).epW := by
  obtain ⟨n, hn, h⟩ := S.ac _ l hl .e1
  rw [show c + 2 • z + (0, 1) + Dir.vec .e1 = c + 2 • z + (1, 1) by site_eq] at hn
  rw [S.ne_eq z hn] at h
  exact (matchE_parts (fits_e1.1 h)).2.1.trans (F_epW _)

theorem se_facts (z : Plane) {l : Letter} (hl : l ∈ L (c + 2 • z + (1, 0))) :
    ¬ l.base.thick.IsCorner ∧ (l.base.black = .B ∨ l.base.black = .C) ∧ l.b1 = false ∧
      (l.base.black = .B → l.base.thick.epN ≠ .r0) ∧
      (l.base.black = .C → l.base.thick.epN ≠ .r2) :=
  T3_c (S.fam.inA _ l hl) (thin_at S.phase hl)

theorem nw_facts (z : Plane) {l : Letter} (hl : l ∈ L (c + 2 • z + (0, 1))) :
    ¬ l.base.thick.IsCorner ∧ (l.base.black = .D ∨ l.base.black = .E) ∧ l.b2 = false ∧
      (l.base.black = .D → l.base.thick.epE ≠ .r3) ∧
      (l.base.black = .E → l.base.thick.epE ≠ .r1) :=
  T3_d (S.fam.inA _ l hl) (thin_at S.phase hl)

theorem se_black_B (z : Plane) {l : Letter} (hl : l ∈ L (c + 2 • z + (1, 0)))
    (h : (θ z).epS = .r2) : l.base.black = .B := by
  obtain ⟨-, hBC, -, -, hC⟩ := S.se_facts z hl
  rcases hBC with h' | h'
  · exact h'
  · exact absurd (by rw [S.se_epN z hl, h]) (hC h')

theorem se_black_C (z : Plane) {l : Letter} (hl : l ∈ L (c + 2 • z + (1, 0)))
    (h : (θ z).epS = .r0) : l.base.black = .C := by
  obtain ⟨-, hBC, -, hB, -⟩ := S.se_facts z hl
  rcases hBC with h' | h'
  · exact absurd (by rw [S.se_epN z hl, h]) (hB h')
  · exact h'

theorem nw_black_E (z : Plane) {l : Letter} (hl : l ∈ L (c + 2 • z + (0, 1)))
    (h : (θ z).epW = .r3) : l.base.black = .E := by
  obtain ⟨-, hDE, -, hD, -⟩ := S.nw_facts z hl
  rcases hDE with h' | h'
  · exact absurd (by rw [S.nw_epE z hl, h]) (hD h')
  · exact h'

theorem nw_black_D (z : Plane) {l : Letter} (hl : l ∈ L (c + 2 • z + (0, 1)))
    (h : (θ z).epW = .r1) : l.base.black = .D := by
  obtain ⟨-, hDE, -, -, hE⟩ := S.nw_facts z hl
  rcases hDE with h' | h'
  · exact h'
  · exact absurd (by rw [S.nw_epE z hl, h]) (hE h')

/-! ### Neighbours -/

theorem nbE (z : Plane) {a : Letter} (ha : a ∈ L (c + 2 • z)) :
    ∃ l ∈ L (c + 2 • z + (1, 0)), a.MatchE l := by
  obtain ⟨l, hl, h⟩ := S.ac _ a ha .e1
  exact ⟨l, hl, fits_e1.1 h⟩

theorem nbN (z : Plane) {a : Letter} (ha : a ∈ L (c + 2 • z)) :
    ∃ l ∈ L (c + 2 • z + (0, 1)), a.MatchN l := by
  obtain ⟨l, hl, h⟩ := S.ac _ a ha .e2
  exact ⟨l, hl, fits_e2.1 h⟩

theorem nbW (z : Plane) {a : Letter} (ha : a ∈ L (c + 2 • z)) :
    ∃ l ∈ L (c + 2 • (z + (-1, 0)) + (1, 0)), l.MatchE a := by
  obtain ⟨l, hl, h⟩ := S.ac _ a ha .e1'
  rw [show c + 2 • z + Dir.vec .e1' = c + 2 • (z + (-1, 0)) + (1, 0) by site_eq] at hl
  exact ⟨l, hl, fits_e1'.1 h⟩

theorem nbS (z : Plane) {a : Letter} (ha : a ∈ L (c + 2 • z)) :
    ∃ l ∈ L (c + 2 • (z + (0, -1)) + (0, 1)), l.MatchN a := by
  obtain ⟨l, hl, h⟩ := S.ac _ a ha .e2'
  rw [show c + 2 • z + Dir.vec .e2' = c + 2 • (z + (0, -1)) + (0, 1) by site_eq] at hl
  exact ⟨l, hl, fits_e2'.1 h⟩

/-- From the south-east site of `z` to the south-west site of `z + e₁`. -/
theorem seE (z : Plane) {l : Letter} (hl : l ∈ L (c + 2 • z + (1, 0))) :
    ∃ a' ∈ L (c + 2 • (z + (1, 0))), l.MatchE a' := by
  obtain ⟨a', ha', h⟩ := S.ac _ l hl .e1
  rw [show c + 2 • z + (1, 0) + Dir.vec .e1 = c + 2 • (z + (1, 0)) by site_eq] at ha'
  exact ⟨a', ha', fits_e1.1 h⟩

/-- From the south-east site of `z` to the south-west site of `z`. -/
theorem seW (z : Plane) {l : Letter} (hl : l ∈ L (c + 2 • z + (1, 0))) :
    ∃ a' ∈ L (c + 2 • z), a'.MatchE l := by
  obtain ⟨a', ha', h⟩ := S.ac _ l hl .e1'
  rw [show c + 2 • z + (1, 0) + Dir.vec .e1' = c + 2 • z by site_eq] at ha'
  exact ⟨a', ha', fits_e1'.1 h⟩

/-- From the north-west site of `z` to the south-west site of `z + e₂`. -/
theorem nwN (z : Plane) {l : Letter} (hl : l ∈ L (c + 2 • z + (0, 1))) :
    ∃ a' ∈ L (c + 2 • (z + (0, 1))), l.MatchN a' := by
  obtain ⟨a', ha', h⟩ := S.ac _ l hl .e2
  rw [show c + 2 • z + (0, 1) + Dir.vec .e2 = c + 2 • (z + (0, 1)) by site_eq] at ha'
  exact ⟨a', ha', fits_e2.1 h⟩

/-- From the north-west site of `z` to the south-west site of `z`. -/
theorem nwS (z : Plane) {l : Letter} (hl : l ∈ L (c + 2 • z + (0, 1))) :
    ∃ a' ∈ L (c + 2 • z), a'.MatchN l := by
  obtain ⟨a', ha', h⟩ := S.ac _ l hl .e2'
  rw [show c + 2 • z + (0, 1) + Dir.vec .e2' = c + 2 • z by site_eq] at ha'
  exact ⟨a', ha', fits_e2'.1 h⟩

/-! ### The four cases (proof of `thr:coarse`(a)) -/

/-- `thr:coarse`(a), case `θ_z = b`: `ω = A`, `κ` is a corner, and both bits are `1`. -/
theorem b_case (z : Plane) (hz : θ z = .b) {a : Letter} (ha : a ∈ L (c + 2 • z)) :
    a.base.black = .A ∧ a.base.thick.IsCorner ∧ a.b1 = true ∧ a.b2 = true := by
  have hA := S.fam.inA _ a ha
  obtain ⟨lE, hlE, mE⟩ := S.nbE z ha
  obtain ⟨lN, hlN, mN⟩ := S.nbN z ha
  obtain ⟨lW, hlW, mW⟩ := S.nbW z ha
  obtain ⟨lS, hlS, mS⟩ := S.nbS z ha
  have pE := matchE_parts mE
  have pN := matchN_parts mN
  have pW := matchE_parts mW
  have pS := matchN_parts mS
  have hω : a.base.black = .A := by
    have h1 : a.base.black.bitE = false := by
      rw [pE.2.2.1, S.se_black_B z hlE (by rw [hz]; rfl)]; rfl
    have h2 : a.base.black.bitN = false := by
      rw [pN.2.2.1, S.nw_black_E z hlN (by rw [hz]; rfl)]; rfl
    exact (T5_black _).1.1 ⟨h2, h1⟩
  have hκ : a.base.thick.IsCorner := (T5_letter hA (S.sw_thin z ha)).1 hω
  obtain ⟨k, hk⟩ := exists_corner hκ
  refine ⟨hω, hκ, ?_, ?_⟩
  · -- the lines north and south of `𝔞` have red horizontal atoms
    by_contra hb
    rw [Bool.not_eq_true] at hb
    obtain ⟨hNc, -, hNb2, -⟩ := S.nw_facts z hlN
    obtain ⟨hSc, -, hSb2, -⟩ := S.nw_facts _ hlS
    have rN : lN.base.thick.epE.IsRed := by rw [S.nw_epE z hlN, hz]; trivial
    have rS : lS.base.thick.epE.IsRed := by
      rw [S.nw_epE _ hlS, S.θ_e2', hz]; trivial
    have gN : ¬ lN.base.thick.epN.IsRed := fun h =>
      T4' (S.fam.inA _ _ hlN) hNc (by rw [hNb2, ← pN.2.2.2, hb]) h rN
    have gS : ¬ lS.base.thick.epN.IsRed := fun h =>
      T4' (S.fam.inA _ _ hlS) hSc (by rw [hSb2, pS.2.2.2, hb]) h rS
    rw [thick_epN_eq_epS hNc, ← pN.2.1, hk] at gN
    rw [pS.2.1, hk] at gS
    exact gN ((T1 k).1.2 gS)
  · -- the lines east and west of `𝔞` have red vertical atoms
    by_contra hb
    rw [Bool.not_eq_true] at hb
    obtain ⟨hEc, -, hEb1, -⟩ := S.se_facts z hlE
    obtain ⟨hWc, -, hWb1, -⟩ := S.se_facts _ hlW
    have rE : lE.base.thick.epN.IsRed := by rw [S.se_epN z hlE, hz]; trivial
    have rW : lW.base.thick.epN.IsRed := by
      rw [S.se_epN _ hlW, S.θ_e1', hz]; trivial
    have gE : ¬ lE.base.thick.epE.IsRed :=
      T4' (S.fam.inA _ _ hlE) hEc (by rw [hEb1, ← pE.2.2.2, hb]) rE
    have gW : ¬ lW.base.thick.epE.IsRed :=
      T4' (S.fam.inA _ _ hlW) hWc (by rw [hWb1, pW.2.2.2, hb]) rW
    rw [thick_epE_eq_epW hEc, ← pE.2.1, hk] at gE
    rw [pW.2.1, hk] at gW
    exact gE ((T1 k).2.2 gW)

/-- `thr:coarse`(a), case `θ_z = c`: `ω ∈ {B, C}` and `b₁ = 1`. -/
theorem c_case (z : Plane) (hz : θ z = .c) {a : Letter} (ha : a ∈ L (c + 2 • z)) :
    (a.base.black = .B ∨ a.base.black = .C) ∧ a.b1 = true := by
  obtain ⟨lN, hlN, mN⟩ := S.nbN z ha
  obtain ⟨lS, hlS, mS⟩ := S.nbS z ha
  have pN := matchN_parts mN
  have pS := matchN_parts mS
  refine ⟨?_, ?_⟩
  · have h1 : a.base.black.bitN = true := by
      rw [pN.2.2.1, S.nw_black_D z hlN (by rw [hz]; rfl)]; rfl
    have h2 : a.base.black.bitS = false := by
      rw [← pS.2.2.1, S.nw_black_E _ hlS (by rw [S.θ_e2', hz]; rfl)]; rfl
    exact (T5_black _).2.1.1 ⟨h1, h2⟩
  · obtain ⟨a', ha', m'⟩ := S.nwN z hlN
    have hb := (S.b_case (z + (0, 1)) (by rw [S.θ_e2, hz]; rfl) ha').2.2.1
    rw [pN.2.2.2, (matchN_parts m').2.2.2, hb]

/-- `thr:coarse`(a), case `θ_z = d`: `ω ∈ {D, E}` and `b₂ = 1`. -/
theorem d_case (z : Plane) (hz : θ z = .d) {a : Letter} (ha : a ∈ L (c + 2 • z)) :
    (a.base.black = .D ∨ a.base.black = .E) ∧ a.b2 = true := by
  obtain ⟨lE, hlE, mE⟩ := S.nbE z ha
  obtain ⟨lW, hlW, mW⟩ := S.nbW z ha
  have pE := matchE_parts mE
  have pW := matchE_parts mW
  refine ⟨?_, ?_⟩
  · have h1 : a.base.black.bitE = true := by
      rw [pE.2.2.1, S.se_black_C z hlE (by rw [hz]; rfl)]; rfl
    have h2 : a.base.black.bitW = false := by
      rw [← pW.2.2.1, S.se_black_B _ hlW (by rw [S.θ_e1', hz]; rfl)]; rfl
    exact (T5_black _).2.2.1 ⟨h1, h2⟩
  · obtain ⟨a', ha', m'⟩ := S.seE z hlE
    have hb := (S.b_case (z + (1, 0)) (by rw [S.θ_e1, hz]; rfl) ha').2.2.2
    rw [pE.2.2.2, (matchE_parts m').2.2.2, hb]

/-- **`thr:coarse`(a)**, first claim: every `𝔞↑` is a letter of `𝔸`. -/
theorem up_inA (z : Plane) {a : Letter} (ha : a ∈ L (c + 2 • z)) : (up (θ z) a).InA := by
  have hA := S.fam.inA _ a ha
  have hth := S.sw_thin z ha
  obtain ⟨⟨θa, κ, ω⟩, b1, b2⟩ := a
  simp only at hth
  subst hth
  obtain ⟨hO, -, -, h3, h4⟩ := hA
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [up]
    cases hθ : θ z
    · exact hO
    · obtain ⟨hω, hκ, -⟩ := S.b_case z hθ ha
      obtain ⟨k, rfl⟩ := exists_corner hκ
      simp only at hω
      subst hω
      exact inO_b_corner k
    · exact (inO_c_iff (S.c_case z hθ ha).1 κ).2 hO
    · exact (inO_d_iff (S.d_case z hθ ha).1 κ).2 hO
  · intro h
    simp only [up] at h ⊢
    rcases h with h | h
    · have := (S.b_case z h ha).2.2.1; simp only at this; simp [this]
    · have := (S.c_case z h ha).2; simp only at this; simp [this]
  · intro h
    simp only [up] at h ⊢
    rcases h with h | h
    · have := (S.b_case z h ha).2.2.2; simp only at this; simp [this]
    · have := (S.d_case z h ha).2; simp only at this; simp [this]
  · intro h
    have := h3 h
    simp only at this
    simp [up, this]
  · intro h
    simp only [up]
    have := h4 h
    simpa using this

end CoarseSetup

/-- **`thr:coarse`(a)**, second claim: `𝔞 ↦ 𝔞↑` is injective on letters of thin type `a`. -/
theorem up_inj (t : Thin) {a a' : Letter} (ha : a.base.thin = .a) (ha' : a'.base.thin = .a)
    (h : up t a = up t a') : a = a' := by
  obtain ⟨⟨θ, κ, ω⟩, b1, b2⟩ := a
  obtain ⟨⟨θ', κ', ω'⟩, b1', b2'⟩ := a'
  simp only [up, Letter.mk.injEq, Formal.mk.injEq, Bool.not_inj_iff] at h ha ha'
  obtain ⟨⟨-, rfl, rfl⟩, rfl, rfl⟩ := h
  subst ha ha'
  rfl

/-! ## `thr:coarse`(b) -/

/-- Coarsening across a line of thin type `c`: matching in direction `e₁`. -/
theorem up_matchE {t t' : Thin} {a l a' : Letter} (ht : t' = t.horiz)
    (hl : ¬ l.base.thick.IsCorner) (hlb : l.base.black = .B ∨ l.base.black = .C)
    (h1 : a.MatchE l) (h2 : l.MatchE a') : (up t a).MatchE (up t' a') := by
  have p1 := matchE_parts h1
  have p2 := matchE_parts h2
  refine Letter.matchE_iff.2 ⟨Formal.matchE_iff.2 ⟨(Thin.epE_eq_epW_iff _ _).2 ht, ?_, ?_⟩, ?_⟩
  · exact p1.2.1.trans ((thick_epE_eq_epW hl).symm.trans p2.2.1)
  · exact p1.2.2.1.trans ((bitE_eq_bitW hlb).symm.trans p2.2.2.1)
  · simp only [up, p1.2.2.2, p2.2.2.2]

/-- Coarsening across a line of thin type `d`: matching in direction `e₂`. -/
theorem up_matchN {t t' : Thin} {a l a' : Letter} (ht : t' = t.vert)
    (hl : ¬ l.base.thick.IsCorner) (hlb : l.base.black = .D ∨ l.base.black = .E)
    (h1 : a.MatchN l) (h2 : l.MatchN a') : (up t a).MatchN (up t' a') := by
  have p1 := matchN_parts h1
  have p2 := matchN_parts h2
  refine Letter.matchN_iff.2 ⟨Formal.matchN_iff.2 ⟨(Thin.epN_eq_epS_iff _ _).2 ht, ?_, ?_⟩, ?_⟩
  · exact p1.2.1.trans ((thick_epN_eq_epS hl).symm.trans p2.2.1)
  · exact p1.2.2.1.trans ((bitN_eq_bitS hlb).symm.trans p2.2.2.1)
  · simp only [up, p1.2.2.2, p2.2.2.2]

namespace CoarseSetup

variable {L : Plane → Set Letter} {c : Plane} {θ : Plane → Thin} (S : CoarseSetup L c θ)
include S

/-- **`thr:coarse`(b)**: `𝓛↑` is a list family. -/
theorem coarsen_family : IsListFamily (coarsen L c θ) where
  nonempty z := (S.fam.nonempty _).image _
  inA z := by
    rintro _ ⟨a, ha, rfl⟩
    exact S.up_inA z ha

omit S in
/-- **`thr:coarse`(b)**: every letter of `𝓛↑(z)` has thin type `θ_z`. -/
theorem coarsen_thin (z : Plane) : ∀ x ∈ coarsen L c θ z, x.base.thin = θ z := by
  rintro _ ⟨a, -, rfl⟩
  rfl

/-- **`thr:coarse`(b)**: `𝓛↑` is arc consistent. -/
theorem coarsen_ac : ArcConsistent (coarsen L c θ) := by
  rintro z _ ⟨a, ha, rfl⟩ d
  cases d
  · obtain ⟨l, hl, m1⟩ := S.nbE z ha
    obtain ⟨a', ha', m2⟩ := S.seE z hl
    obtain ⟨hlc, hlb, -⟩ := S.se_facts z hl
    exact ⟨up (θ (z + (1, 0))) a', ⟨a', ha', rfl⟩,
      fits_e1.2 (up_matchE (S.θ_e1 z) hlc hlb m1 m2)⟩
  · obtain ⟨l, hl, m1⟩ := S.nbW z ha
    obtain ⟨a', ha', m2⟩ := S.seW _ hl
    obtain ⟨hlc, hlb, -⟩ := S.se_facts _ hl
    refine ⟨up (θ (z + (-1, 0))) a', ⟨a', ha', rfl⟩, fits_e1'.2 (up_matchE ?_ hlc hlb m2 m1)⟩
    rw [S.θ_e1', Thin.horiz_horiz]
  · obtain ⟨l, hl, m1⟩ := S.nbN z ha
    obtain ⟨a', ha', m2⟩ := S.nwN z hl
    obtain ⟨hlc, hlb, -⟩ := S.nw_facts z hl
    exact ⟨up (θ (z + (0, 1))) a', ⟨a', ha', rfl⟩,
      fits_e2.2 (up_matchN (S.θ_e2 z) hlc hlb m1 m2)⟩
  · obtain ⟨l, hl, m1⟩ := S.nbS z ha
    obtain ⟨a', ha', m2⟩ := S.nwS _ hl
    obtain ⟨hlc, hlb, -⟩ := S.nw_facts _ hl
    refine ⟨up (θ (z + (0, -1))) a', ⟨a', ha', rfl⟩, fits_e2'.2 (up_matchN ?_ hlc hlb m2 m1)⟩
    rw [S.θ_e2', Thin.vert_vert]

/-- **`thr:coarse`(b)**: in particular `𝓛↑` has a thin phase (by `thr:thin`). -/
theorem coarsen_phase : ∃ c', HasThinPhase (coarsen L c θ) c' := by
  obtain ⟨c', hc', -⟩ := thr_thin S.coarsen_ac (coarsen_thin 0)
  exact ⟨c', hc'⟩

/-! ## `thr:coarse`(c) -/

theorem ne_singleton (z : Plane) : L (c + 2 • z + (1, 1)) = {bLetter (θ z)} := by
  refine Set.eq_singleton_iff_nonempty_unique_mem.2 ⟨S.fam.nonempty _, fun y hy => S.ne_eq z hy⟩

/-- **`thr:coarse`(c)**: if `𝓛↑(z) = {𝔠}`, then `𝓛(c + 2z + ς) = {φ'(𝔠)(ς)}` for every
`ς ∈ {0,1}²` (children indexed by two Booleans, `ς = (bitZ s₁, bitZ s₂)`). -/
theorem coarsen_singleton (z : Plane) {cc : Letter} (h : coarsen L c θ z = {cc}) (s1 s2 : Bool) :
    L (c + 2 • z + (bitZ s1, bitZ s2)) = {cc.child s1 s2} := by
  obtain ⟨a0, ha0, hcc⟩ : cc ∈ coarsen L c θ z := h ▸ rfl
  subst hcc
  have hth0 := S.sw_thin z ha0
  have hsw : L (c + 2 • z) = {a0} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨ha0, fun a ha => ?_⟩
    have : up (θ z) a ∈ coarsen L c θ z := ⟨a, ha, rfl⟩
    rw [h, Set.mem_singleton_iff] at this
    exact up_inj _ (S.sw_thin z ha) hth0 this
  obtain ⟨⟨θa, κ, ω⟩, b1, b2⟩ := a0
  simp only at hth0
  subst hth0
  cases s1 <;> cases s2
  · -- `ς = (0,0)`
    change L (c + 2 • z + (0, 0)) = _
    rw [show c + 2 • z + ((0 : ℤ), (0 : ℤ)) = c + 2 • z by site_eq, hsw]
    simp [up, Letter.child, Formal.child]
  · -- `ς = (0,1)`
    change L (c + 2 • z + (0, 1)) = _
    refine Set.eq_singleton_iff_nonempty_unique_mem.2 ⟨S.fam.nonempty _, fun l hl => ?_⟩
    obtain ⟨hlc, hDE, hb2, -⟩ := S.nw_facts z hl
    obtain ⟨m, hm, hfit⟩ := S.nwS z hl
    rw [hsw, Set.mem_singleton_iff] at hm
    subst hm
    have p := matchN_parts hfit
    obtain ⟨α, γ, hlκ⟩ := exists_line hlc
    have hγ := S.nw_epE z hl
    rw [hlκ] at hγ p
    obtain ⟨⟨lθ, lκ, lω⟩, lb1, lb2⟩ := l
    simp only at hlκ hb2 hDE hγ p ⊢
    have hlθ : lθ = .d := thin_at S.phase hl
    subst hlκ hb2 hlθ
    have hω := nw_unique ω lω hDE p.2.2.1.symm
    simp only [Thick.epS, Thick.epE] at hγ p
    simp [up, Letter.child, Formal.child, hγ, p.2.1, hω, p.2.2.2]
  · -- `ς = (1,0)`
    change L (c + 2 • z + (1, 0)) = _
    refine Set.eq_singleton_iff_nonempty_unique_mem.2 ⟨S.fam.nonempty _, fun l hl => ?_⟩
    obtain ⟨hlc, hBC, hb1, -⟩ := S.se_facts z hl
    obtain ⟨m, hm, hfit⟩ := S.seW z hl
    rw [hsw, Set.mem_singleton_iff] at hm
    subst hm
    have p := matchE_parts hfit
    obtain ⟨α, γ, hlκ⟩ := exists_line hlc
    have hα := S.se_epN z hl
    rw [hlκ] at hα p
    obtain ⟨⟨lθ, lκ, lω⟩, lb1, lb2⟩ := l
    simp only at hlκ hb1 hBC hα p ⊢
    have hlθ : lθ = .c := thin_at S.phase hl
    subst hlκ hb1 hlθ
    have hω := se_unique ω lω hBC p.2.2.1.symm
    simp only [Thick.epW, Thick.epN] at hα p
    simp [up, Letter.child, Formal.child, hα, p.2.1, hω, p.2.2.2]
  · -- `ς = (1,1)`
    change L (c + 2 • z + (1, 1)) = _
    rw [S.ne_singleton z]
    rfl

end CoarseSetup

end FNE.Three
