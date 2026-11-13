/-
Finite physical contours for the three-box marked closure (ld:contours).
REUSE: generic UND grouped_terminal_estimate, connected witness and span.
ADAPT: physical projection of UND.Raw. NEW: actual-terminal bracket, from Bracket.
The estimate 130e <= 1440(f-1) counts distinct physical flags, not copies.
-/
import ForgettingLower.Geometry.Potentials
import ForgettingLower.Contour.Bracket

set_option autoImplicit false

noncomputable section

namespace FLD.Geometry

open Relation UND.Contour FNE.EdgeCount
section Contour

variable {E : ℤ → ISite → Prop} {t0 : ℤ}

theorem mf_of_reach {a b : Pt} (h : (sys E t0).Reach a b) (ha : MF E t0 a) : MF E t0 b := by
  induction h with
  | refl => exact ha
  | tail _ hst ih =>
    rcases hst with ⟨hnf, bb, rfl⟩ | ⟨hu, -⟩
    · exact sel_mf hnf bb
    · exact hu.elim

theorem flag_of_term {x : Pt} (hmf : MF E t0 x) (ht : (sys E t0).IsTerm x) : E x.2 x.1 := by
  by_contra hE
  exact ht.1 ⟨hmf, hE⟩

theorem gLen_eq_gBin (c : Option (Fin 2)) (x : Pt) :
    (sys E t0).gLen c x = (sys E t0).gBin c x := by
  refine (sys E t0).g_induction c (P := fun x => (sys E t0).gLen c x = (sys E t0).gBin c x)
    (fun x h ih => ?_) (fun x h => ?_) x
  · rcases h with h | h
    · rw [(sys E t0).gLen_of_step c (Or.inl h), (sys E t0).gBin_of_NF c h, ih]
    · exact h.elim
  · rw [(sys E t0).gLen_of_isTerm c h, (sys E t0).gBin_of_isTerm c h]

theorem armEdge_spec {P : Finset (GroupedSystem.Pole Pt (Option (Fin 2)))} (hP : ∀ σ ∈ P, NFm E t0 σ.loc) :
    ∀ d ∈ (sys E t0).armEdges P, ∃ x b, NFm E t0 x ∧ d = s(x, (sys E t0).sup x b) := by
  intro d hd
  obtain ⟨σ, hσ, hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨c, -, hd⟩ := Finset.mem_biUnion.mp hd
  rcases Finset.mem_insert.mp hd with rfl | hd
  · exact ⟨σ.loc, σ.fs c, hP σ hσ, rfl⟩
  · obtain ⟨a, -, hna, rfl⟩ := (sys E t0).gEdges_spec c _ d hd
    rcases hna with hna | hna
    · exact ⟨a, _, hna, by rw [(sys E t0).g_of_NF hna]⟩
    · exact hna.elim

theorem exists_edge_of_reach {V : Type*} {K : Finset (Sym2 V)} {a b : V} (h : Reach K a b)
    (hne : a ≠ b) : ∃ d ∈ K, b ∈ d := by
  rcases h.cases_tail with rfl | ⟨c, -, hc⟩
  · exact absurd rfl hne
  · exact ⟨_, hc, Sym2.mem_mk_right _ _⟩

variable (E) in
/-- A full physical contour: distinct flags, charge cost, graph connectivity,
root-relative span and lower bounds by actual selected terminals. -/
def IsContour (x : Pt) (e : ℕ) (Fl : Finset Pt) (K : Finset (Sym2 Pt)) : Prop :=
  1 ≤ Fl.card ∧ 130 * e ≤ 1440 * (Fl.card - 1) ∧ (∀ y ∈ Fl, E y.2 y.1) ∧
    (∀ y ∈ Fl, x.2 - e ≤ y.2 ∧ y.2 ≤ x.2) ∧ ConnectedAt K x ∧ K.card ≤ e ∧
    UND.Counting.InGraph nbr K ∧ (∀ y ∈ Fl, y = x ∨ ∃ d ∈ K, y ∈ d) ∧
    (∀ d ∈ K, ∀ v ∈ d, ∃ y ∈ Fl, y.2 ≤ v.2 ∧ v.2 ≤ x.2)

theorem isContour_flag {x : Pt} (hE : E x.2 x.1) : IsContour E x 0 {x} ∅ := by
  refine ⟨by simp, by simp, fun y hy => ?_, fun y hy => ?_, fun d hd => by simp at hd, by simp,
    fun a b h => by simp at h, fun y hy => Or.inl (Finset.mem_singleton.mp hy), fun d hd => by simp at hd⟩
  · rw [Finset.mem_singleton.mp hy]; exact hE
  · rw [Finset.mem_singleton.mp hy]; simp

/-- Specialize the generic grouped-terminal estimate to three charges. -/
theorem exists_contour_nf {x : Pt} (hx : NFm E t0 x) : ∃ e Fl K, IsContour E x e Fl K := by
  classical
  obtain ⟨P, hroot, hvalid, hlink, hinj, hsurj, hb⟩ :=
    (sys E t0).grouped_terminal_estimate isPotential_psi (by norm_num)
      ((sys E t0).hosc_singleton (ψ := psi) (fun _ _ _ _ h => h)) (ρ := x) hx
  have hC : Fintype.card (Option (Fin 2)) = 3 := by simp
  rw [hC] at hb
  push_cast at hb
  have hPnf : ∀ σ ∈ P, NFm E t0 σ.loc := fun σ hσ => (hvalid σ hσ).2
  have hmfx : MF E t0 x := hx.1
  have hreach : ∀ σ ∈ P, ∀ c, (sys E t0).Reach x ((sys E t0).pEnd σ c) := fun σ hσ c =>
    ((hvalid σ hσ).1.trans ((sys E t0).reach_sup (hvalid σ hσ).2 _)).trans
      ((sys E t0).reach_gEnd c _)
  have hflag : ∀ σ ∈ P, ∀ c, E ((sys E t0).pEnd σ c).2 ((sys E t0).pEnd σ c).1 :=
    fun σ hσ c => flag_of_term (mf_of_reach (hreach σ hσ c) hmfx) ((sys E t0).pEnd_isTerm σ c)
  have hspan := (sys E t0).witness_span Prod.snd
    (fun θ b _ => by show θ.2 - 1 + 1 = θ.2; ring) (fun θ h => h.elim)
    (fun φ φ' _ _ h => congrArg Prod.snd h) hvalid hlink
  have hbracket := FLD.Contour.witness_terminal_bracket (sys E t0) Prod.snd
    (fun θ b _ => by show θ.2 - 1 + 1 = θ.2; ring) (fun θ h => h.elim)
    (fun φ φ' _ _ h => congrArg Prod.snd h) none hvalid hsurj
  -- the edges: the witness without loops; they are arm edges
  have hKarm : ((sys E t0).witness P).filter (fun d => ¬ d.IsDiag) ⊆ (sys E t0).armEdges P := by
    intro d hd
    obtain ⟨hdw, hnd⟩ := Finset.mem_filter.mp hd
    rcases Finset.mem_union.mp hdw with h | h
    · exact h
    · exfalso
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
      have heq : (sys E t0).pEnd p.1.1 p.1.2 = (sys E t0).pEnd p.2.1 p.2.2 :=
        ((@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).mp hp).2
      exact hnd (by rw [heq]; exact Sym2.mk_isDiag_iff.mpr rfl)
  have harm := armEdge_spec hPnf
  -- each end lies on a non-loop arm edge
  have hendK : ∀ σ ∈ P, ∀ c, ∃ d ∈ ((sys E t0).witness P).filter (fun d => ¬ d.IsDiag),
      (sys E t0).pEnd σ c ∈ d := by
    intro σ hσ c
    have hr := ((sys E t0).pEdges_reach σ c).2
    have hne : σ.loc ≠ (sys E t0).pEnd σ c := by
      intro h
      have h1 := (sys E t0).time_le_of_reach Prod.snd
        (fun θ b _ => by show θ.2 - 1 + 1 = θ.2; ring) (fun θ h => h.elim)
        ((sys E t0).reach_gEnd c ((sys E t0).pFirst σ c))
      have h2 : ((sys E t0).pFirst σ c).2 = σ.loc.2 - 1 := rfl
      have h3 : ((sys E t0).pEnd σ c).2 = σ.loc.2 := by rw [← h]
      unfold GroupedSystem.pEnd at h3
      omega
    obtain ⟨d, hd, hmem⟩ := exists_edge_of_reach hr hne
    have hdw := (sys E t0).pEdges_subset_witness hσ c hd
    have hda : d ∈ (sys E t0).armEdges P :=
      Finset.mem_biUnion.mpr ⟨σ, hσ, Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, hd⟩⟩
    obtain ⟨y, b, hy, rfl⟩ := harm d hda
    exact ⟨_, Finset.mem_filter.mpr ⟨hdw, not_isDiag_par _ _ _⟩, hmem⟩
  have hlen : ∀ σ c, (sys E t0).pLen σ c = (sys E t0).pBin σ c := fun σ c => by
    unfold GroupedSystem.pLen GroupedSystem.pBin
    rw [gLen_eq_gBin]
  have hinjE : Set.InjOn (fun σ => (sys E t0).pEnd σ none) (P : Set (GroupedSystem.Pole Pt (Option (Fin 2)))) :=
    fun σ hσ σ' hσ' h => hinj none σ hσ σ' hσ' h
  have hcard : (P.image (fun σ => (sys E t0).pEnd σ none)).card = P.card :=
    Finset.card_image_of_injOn hinjE
  have hP1 : 1 ≤ P.card := Finset.card_pos.mpr ⟨_, hroot⟩
  refine ⟨∑ σ ∈ P, ∑ c, (sys E t0).pBin σ c, P.image (fun σ => (sys E t0).pEnd σ none),
    ((sys E t0).witness P).filter (fun d => ¬ d.IsDiag), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcard]; exact hP1
  · rw [hcard]
    have : ((∑ σ ∈ P, ∑ c, (sys E t0).pBin σ c : ℕ) : ℤ) =
        ∑ σ ∈ P, ∑ c, ((sys E t0).pBin σ c : ℤ) := by push_cast; rfl
    have hb' : (130 : ℤ) * ((∑ σ ∈ P, ∑ c, (sys E t0).pBin σ c : ℕ) : ℤ) ≤
        1440 * ((P.card : ℤ) - 1) := by rw [this]; linarith
    omega
  · intro y hy
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hy
    exact hflag σ hσ none
  · intro y hy
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨d, hd, hmem⟩ := hendK σ hσ none
    have := hspan d (Finset.mem_filter.mp hd).1 _ hmem
    push_cast
    constructor <;> linarith [this.1, this.2]
  · exact UND.Counting.connectedAt_filter_not_diag ((sys E t0).witness_connected hlink)
  · refine (Finset.card_le_card hKarm).trans (((sys E t0).armEdges_card_le P).trans ?_)
    exact le_of_eq (Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun c _ => hlen σ c)
  · intro a b hab
    obtain ⟨y, bb, hy, he⟩ := harm _ (hKarm hab)
    exact inGraph_par (sel_box hy bb) a b he
  · intro y hy
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hy
    exact Or.inr (hendK σ hσ none)
  · intro d hd v hv
    obtain ⟨σ, hσ, hlo, hup⟩ := hbracket d (Finset.mem_filter.mp hd).1 v hv
    exact ⟨_, Finset.mem_image.mpr ⟨σ, hσ, rfl⟩, hlo, hup⟩

/-- Every finitarily marked root has a complete finite physical contour. -/
theorem exists_contour {x : Pt} (hx : marked E x.2 x.1) : ∃ e Fl K, IsContour E x e Fl K := by
  by_cases hE : E x.2 x.1
  · exact ⟨0, {x}, ∅, isContour_flag hE⟩
  · obtain ⟨n, hn⟩ := hx
    have hmf : MF E (x.2 - n) x :=
      ⟨by omega, by rwa [show (x.2 - (x.2 - n)).toNat = n by omega]⟩
    exact exists_contour_nf (t0 := x.2 - n) ⟨hmf, hE⟩

end Contour

/-- The exact charge estimate implies the printed integer contour cost. -/
theorem IsContour.edges_le {E : ℤ → ISite → Prop} {x : Pt} {e : ℕ}
    {Fl : Finset Pt} {K : Finset (Sym2 Pt)} (h : IsContour E x e Fl K) :
    e ≤ 12 * (Fl.card - 1) := by
  have hi := h.2.1
  omega

/-- Choose an ACTUAL earliest terminal. Every physical vertex is in its closed
slab, whose span is at most 12(f-1); the full contour remains intact. -/
theorem IsContour.exists_earliest {E : ℤ → ISite → Prop} {x : Pt} {e : ℕ}
    {Fl : Finset Pt} {K : Finset (Sym2 Pt)} (h : IsContour E x e Fl K) :
    ∃ z ∈ Fl, (∀ y ∈ Fl, z.2 ≤ y.2 ∧ y.2 ≤ x.2) ∧
      (∀ d ∈ K, ∀ v ∈ d, z.2 ≤ v.2 ∧ v.2 ≤ x.2) ∧
      x.2 - z.2 ≤ 12 * ((Fl.card : ℤ) - 1) := by
  classical
  have hne : Fl.Nonempty := Finset.card_pos.mp h.1
  let times := Fl.image Prod.snd
  have ht : times.Nonempty := hne.image _
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp (Finset.min'_mem times ht)
  have hmin : ∀ y ∈ Fl, z.2 ≤ y.2 := by
    intro y hy
    rw [heq]
    exact Finset.min'_le times _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  have hs := h.2.2.2.1 z hz
  have hf := h.1
  have hc := h.edges_le
  refine ⟨z, hz, fun y hy => ⟨hmin y hy, (h.2.2.2.1 y hy).2⟩, ?_, ?_⟩
  · intro d hd v hv
    obtain ⟨y, hy, hlo, hup⟩ := h.2.2.2.2.2.2.2.2 d hd v hv
    exact ⟨(hmin y hy).trans hlo, hup⟩
  · omega

end FLD.Geometry