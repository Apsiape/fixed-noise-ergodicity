/-
Concrete finite-path encoding for ld:density. The whole N-edge path is retained,
with every selected parent spur and every full contour, including the last.
No probability or independence assertion is used here.
-/
import ForgettingLower.Contour.Finite
import ForgettingLower.Density.Slabs

set_option autoImplicit false

noncomputable section

namespace FLD.Density

open FLD.Geometry FNE.EdgeCount Relation UND.Contour
open FNE (Plane box)

/-- Edges of the entire finite path. -/
def pathEdges (Q : ℕ → Pt) (N : ℕ) : Finset (Sym2 Pt) :=
  (Finset.range N).image (fun i => s(Q i, Q (i + 1)))

theorem card_pathEdges_le (Q : ℕ → Pt) (N : ℕ) : (pathEdges Q N).card ≤ N :=
  Finset.card_image_le.trans (Finset.card_range N).le

theorem pathEdges_reach (Q : ℕ → Pt) (N : ℕ) :
    ∀ j ≤ N, Reach (pathEdges Q N) (Q 0) (Q j) := by
  intro j
  induction j with
  | zero => intro _; exact ReflTransGen.refl
  | succ j ih =>
    intro hj
    exact (ih (by omega)).tail (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩)

theorem pathEdges_connected (Q : ℕ → Pt) (N : ℕ) : ConnectedAt (pathEdges Q N) (Q 0) := by
  intro d hd v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
  have hi := Finset.mem_range.mp hi
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact pathEdges_reach Q N i (by omega)
  · exact pathEdges_reach Q N (i + 1) (by omega)

theorem pathEdges_inGraph {Q : ℕ → Pt} {N : ℕ}
    (hstep : ∀ k < N, ∃ π, ∃ μ ∈ box 1, Q (k + 1) = par (Q k) π μ) :
    UND.Counting.InGraph nbr (pathEdges Q N) := by
  intro a b hab
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hab
  obtain ⟨π, μ, hμ, hq⟩ := hstep i (Finset.mem_range.mp hi)
  rw [hq] at he
  exact inGraph_par hμ a b he.symm

theorem path_time {Q : ℕ → Pt} {N : ℕ}
    (hstep : ∀ k < N, ∃ π, ∃ μ ∈ box 1, Q (k + 1) = par (Q k) π μ) :
    ∀ k ≤ N, (Q k).2 = (Q 0).2 - k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨π, μ, -, hq⟩ := hstep k (by omega)
    rw [hq, par_time, ih (by omega)]
    push_cast
    ring

/-- Untruncated data attached to one marked-parent occurrence. -/
structure Attachment where
  π : Provider
  μ : Plane
  e : ℕ
  flags : Finset Pt
  edges : Finset (Sym2 Pt)
  first : Pt
  deriving Inhabited

def AttachSpec (E : ℤ → ISite → Prop) (x : Pt) (d : Attachment) : Prop :=
  d.μ ∈ box 1 ∧ IsContour E (par x d.π d.μ) d.e d.flags d.edges ∧
    d.first ∈ d.flags ∧
    (∀ y ∈ d.flags, d.first.2 ≤ y.2 ∧ y.2 ≤ (par x d.π d.μ).2) ∧
    (∀ a ∈ d.edges, ∀ v ∈ a, d.first.2 ≤ v.2 ∧ v.2 ≤ (par x d.π d.μ).2) ∧
    (par x d.π d.μ).2 - d.first.2 ≤ 12 * ((d.flags.card : ℤ) - 1)

theorem exists_attachment {E : ℤ → ISite → Prop} {x : Pt} (h : H E x) :
    ∃ d, AttachSpec E x d := by
  obtain ⟨μ, hμ, π, hm⟩ := h
  obtain ⟨e, Fl, K, hc⟩ := exists_contour (x := par x π μ) hm
  obtain ⟨z, hz, ht, hv, hs⟩ := hc.exists_earliest
  exact ⟨⟨π, μ, e, Fl, K, z⟩, hμ, hc, hz, ht, hv, hs⟩

open Classical in
/-- Concrete slabs and whole connected-union encoding for a dense finite path.
The finite path is required to be ordinary only at its first N edges. -/
theorem exists_density_encoding {E : ℤ → ISite → Prop} {Q : ℕ → Pt} {N : ℕ}
    (hstep : ∀ k < N, ∃ π, ∃ μ ∈ box 1, Q (k + 1) = par (Q k) π μ)
    (hdense : (N : ℝ) / 1404 ≤ ((Finset.range N).filter (fun i => H E (Q i))).card) :
    ∃ Fl : Finset Pt, ∃ K : Finset (Sym2 Pt),
      (N : ℝ) / 1404 ≤ 12 * (Fl.card : ℝ) ∧
      UND.Counting.IsEncoding nbr (Q 0) (densityCost * Fl.card) K Fl ∧
      pathEdges Q N ⊆ K ∧ (∀ y ∈ Fl, E y.2 y.1) := by
  classical
  let A := (Finset.range N).filter (fun i => H E (Q i))
  have hex : ∀ i, ∃ d : Attachment, i ∈ A → AttachSpec E (Q i) d := by
    intro i
    by_cases hi : i ∈ A
    · obtain ⟨d, hd⟩ := exists_attachment (Finset.mem_filter.mp hi).2
      exact ⟨d, fun _ => hd⟩
    · exact ⟨default, fun h => (hi h).elim⟩
  choose d hd using hex
  let right := fun i => max i (((Q 0).2 - (d i).first.2 - 1).toNat)
  let depth := fun v : Pt => ((Q 0).2 - v.2).toNat
  have htime : ∀ i ∈ A, (Q i).2 = (Q 0).2 - i := by
    intro i hi
    exact path_time hstep i (Nat.le_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hi).1))
  have hr : ∀ i ∈ A, (right i : ℤ) = (Q 0).2 - (d i).first.2 - 1 := by
    intro i hi
    have hdi := hd i hi
    have ht := hdi.2.2.2.1 _ hdi.2.2.1
    have hiT := htime i hi
    simp only [par_time] at ht
    dsimp [right]
    omega
  obtain ⟨S, hS, hcard, hmass, hcost⟩ := exists_density_accounting A right
    (fun i => (d i).flags) depth N (fun i => Nat.le_max_left _ _)
    (fun i hi => (hd i hi).2.1.1)
    (fun i hi => by
      have hs := (hd i hi).2.2.2.2.2
      have hf := (hd i hi).2.1.1
      have hiT := htime i hi
      have hiR := hr i hi
      simp only [par_time] at hs
      omega)
    (fun i hi v hv => by
      have ht := (hd i hi).2.2.2.1 v hv
      have hiT := htime i hi
      have hiR := hr i hi
      simp only [par_time] at ht
      dsimp [depth]
      omega) hdense
  let L := fun i => insert s(Q i, par (Q i) (d i).π (d i).μ) (d i).edges
  let K := pathEdges Q N ∪ S.biUnion L
  have hpath : pathEdges Q N ⊆ K := Finset.subset_union_left
  have hL : ∀ i ∈ S, L i ⊆ K := by
    intro i hi e he
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, he⟩)
  have hspur : ∀ i ∈ S, Reach K (Q 0) (par (Q i) (d i).π (d i).μ) := by
    intro i hi
    have hiN := Finset.mem_range.mp (Finset.mem_filter.mp (hS.1 hi)).1
    refine (GroupedSystem.reach_mono hpath (pathEdges_reach Q N i (by omega))).tail ?_
    exact hL i hi (Finset.mem_insert_self _ _)
  have hconn : ConnectedAt K (Q 0) := by
    intro e he v hv
    rcases Finset.mem_union.mp he with he | he
    · exact GroupedSystem.reach_mono hpath (pathEdges_connected Q N e he v hv)
    · obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
      rcases Finset.mem_insert.mp he with rfl | he
      · rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact GroupedSystem.reach_mono hpath (pathEdges_reach Q N i (by
            have := Finset.mem_range.mp (Finset.mem_filter.mp (hS.1 hi)).1
            omega))
        · exact hspur i hi
      · exact (hspur i hi).trans (GroupedSystem.reach_mono
          (fun a ha => hL i hi (Finset.mem_insert_of_mem ha)) ((hd i (hS.1 hi)).2.1.2.2.2.2.1 e he v hv))
  have hgraph : UND.Counting.InGraph nbr K := by
    intro a b he
    rcases Finset.mem_union.mp he with he | he
    · exact pathEdges_inGraph hstep a b he
    · obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
      rcases Finset.mem_insert.mp he with he | he
      · exact inGraph_par (hd i (hS.1 hi)).1 a b he
      · exact (hd i (hS.1 hi)).2.1.2.2.2.2.2.2.1 a b he
  have hsize : K.card ≤ densityCost * (S.biUnion (fun i => (d i).flags)).card := by
    apply le_trans (Finset.card_union_le _ _)
    apply le_trans (Nat.add_le_add (card_pathEdges_le Q N) Finset.card_biUnion_le)
    apply le_trans (Nat.add_le_add_left (Finset.sum_le_sum (fun i hi => ?_)) N) hcost
    apply (Finset.card_insert_le _ _).trans
    simpa only [Nat.add_comm] using (Nat.add_le_add_right
      ((hd i (hS.1 hi)).2.1.2.2.2.2.2.1.trans (hd i (hS.1 hi)).2.1.edges_le) 1)
  refine ⟨S.biUnion (fun i => (d i).flags), K, hdense.trans ?_,
    ⟨hsize, hgraph, hconn, ?_⟩, hpath, ?_⟩
  · exact_mod_cast hmass
  · intro y hy
    obtain ⟨i, hi, hy⟩ := Finset.mem_biUnion.mp hy
    rcases (hd i (hS.1 hi)).2.1.2.2.2.2.2.2.2.1 y hy with hy | ⟨e, he, hye⟩
    · exact Or.inr ⟨_, hL i hi (Finset.mem_insert_self _ _), hy ▸ Sym2.mem_mk_right _ _⟩
    · exact Or.inr ⟨e, hL i hi (Finset.mem_insert_of_mem he), hye⟩
  · intro y hy
    obtain ⟨i, hi, hy⟩ := Finset.mem_biUnion.mp hy
    exact (hd i (hS.1 hi)).2.1.2.2.1 y hy

end FLD.Density