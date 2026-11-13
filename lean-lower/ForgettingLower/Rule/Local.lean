/- Three-box quorum, checker locality and error counts. The planar checker is reused. -/
import ForgettingLower.Geometry.Marked
import ForgettingNaturalRule.Rule.Local

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace FLD.Rule

open FLD.Geometry (ISite card_Provider)
open FNE (Plane box WangSet)

variable {R : WangSet}

/-! ## R1: the checker in a plane -/

/-- The checker keeps the tile `c` at `u` in the planar layer `y`: `y u = c` and the four cardinal
neighbours are live with matching shared edges (as `FNR.Keeps`). -/
abbrev KeepsI (y : Plane → Option R) (u : Plane) (c : R) : Prop :=
  FNR.Rule.KeepsI y u c

abbrev chkI (y : Plane → Option R) (u : Plane) : Option R := FNR.Rule.chkI y u

theorem chkI_eq_some {y : Plane → Option R} {u : Plane} {c : R} :
    chkI y u = some c ↔ KeepsI y u c := FNR.Rule.chkI_eq_some

theorem mem_cardinal_zero : ((0, 0) : Plane) ∈ cardinal := by decide
theorem mem_cardinal_e1 : ((1, 0) : Plane) ∈ cardinal := by decide
theorem mem_cardinal_w1 : ((-1, 0) : Plane) ∈ cardinal := by decide
theorem mem_cardinal_e2 : ((0, 1) : Plane) ∈ cardinal := by decide
theorem mem_cardinal_w2 : ((0, -1) : Plane) ∈ cardinal := by decide

theorem plane_add_zero (u : Plane) : u + ((0, 0) : Plane) = u := by
  rw [Prod.mk_zero_zero, add_zero]

/-- `Γ ⊆ Λ = {-1, 0, 1}²` (cardinal displacements are Moore displacements). -/
theorem cardinal_sub_box : ∀ γ ∈ cardinal, γ ∈ box 1 := by decide

/-- The checker at `u` reads `y` only on `u + Γ`. -/
theorem chkI_congr {y y' : Plane → Option R} {u : Plane}
    (h : ∀ γ ∈ cardinal, y (u + γ) = y' (u + γ)) : chkI y u = chkI y' u := by
  exact FNR.Rule.chkI_congr h

/-! ## R2: the quorum -/

/-- The number of providers of `w = (u, P)` whose checked reading `C_R(D(·, P + a))(u)` is `s`. -/
def votesI (D : ISite → Option R) (w : ISite) (s : R) : ℕ :=
  (Finset.univ.filter fun π : Provider => chkI (fun u => D (u, w.2 + offset π)) w.1 = some s).card

open Classical in
/-- **The rule `G_R` on `ℤ² × ℤ²`** (Section 12): a live letter with at least `h` checked votes,
`⊥` if none. -/
def GI (D : ISite → Option R) : ISite → Option R := fun w =>
  if h : ∃ s : R, quorum ≤ votesI D w s then some h.choose else none

/-- `2h > q`: at most one live letter reaches the quorum. -/
theorem quorum_unique {D : ISite → Option R} {w : ISite} {s s' : R}
    (hs : quorum ≤ votesI D w s) (hs' : quorum ≤ votesI D w s') : s = s' := by
  classical
  by_contra hne
  unfold votesI at hs hs'
  set A := Finset.univ.filter fun π : Provider =>
    chkI (fun u => D (u, w.2 + offset π)) w.1 = some s with hA
  set B := Finset.univ.filter fun π : Provider =>
    chkI (fun u => D (u, w.2 + offset π)) w.1 = some s' with hB
  have hdisj : Disjoint A B :=
    Finset.disjoint_filter.2 fun π _ h1 h2 => hne (Option.some_injective _ (h1.symm.trans h2))
  have hu := Finset.card_union_of_disjoint hdisj
  have hle := Finset.card_le_univ (A ∪ B)
  rw [card_Provider] at hle
  have hq : q < 2 * quorum := by norm_num [q, K, quorum]
  omega

theorem GI_eq_some_iff {D : ISite → Option R} {w : ISite} {s : R} :
    GI D w = some s ↔ quorum ≤ votesI D w s := by
  unfold GI
  split_ifs with h
  · constructor
    · intro e
      rw [← Option.some_injective _ e]
      exact h.choose_spec
    · intro hs
      rw [quorum_unique h.choose_spec hs]
  · exact ⟨fun e => absurd e (by simp), fun hs => absurd ⟨s, hs⟩ h⟩

/-- A live output has at most `q - h = K = 256` providers whose check fails to return it. -/
theorem card_failed_le {D : ISite → Option R} {w : ISite} {s : R} (h : GI D w = some s) :
    (Finset.univ.filter fun π : Provider =>
      ¬ chkI (fun u => D (u, w.2 + offset π)) w.1 = some s).card ≤ K := by
  have hv := GI_eq_some_iff.1 h
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Provider))
    (fun π : Provider => chkI (fun u => D (u, w.2 + offset π)) w.1 = some s)
  rw [Finset.card_univ, card_Provider] at this
  unfold votesI at hv
  simp only [q, K, quorum] at this hv ⊢
  omega

/-! ## R3: locality and discrepancies -/

/-- `G_R` at `w` reads `D` only on `w + Γ × S`. -/
theorem GI_congr {D D' : ISite → Option R} {w : ISite}
    (h : ∀ γ ∈ cardinal, ∀ π : Provider,
      D (w.1 + γ, w.2 + offset π) = D' (w.1 + γ, w.2 + offset π)) :
    GI D w = GI D' w := by
  have hv : ∀ s, votesI D w s = votesI D' w s := by
    intro s
    unfold votesI
    congr 1
    refine Finset.filter_congr fun π _ => ?_
    rw [chkI_congr (y' := fun u => D' (u, w.2 + offset π)) fun γ hγ => h γ hγ π]
  unfold GI
  simp only [hv]

/-- **A discrepancy has a discrepant actual parent** in `Γ × S`. -/
theorem disc_parent {D D' : ISite → Option R} {w : ISite} (h : GI D w ≠ GI D' w) :
    ∃ γ ∈ cardinal, ∃ π : Provider,
      D (w.1 + γ, w.2 + offset π) ≠ D' (w.1 + γ, w.2 + offset π) := by
  by_contra hc
  push Not at hc
  exact h (GI_congr hc)

/-! ## Trajectories -/

/-- A trajectory of `G_R` from time `s` with replacement flags `E`: at every time `t > s`, off a
flag, the letter is `G_R` of the previous configuration (the update (Section 12) with the flagged
letters left arbitrary). -/
def IsTraj (s : ℤ) (D : ℤ → ISite → Option R) (E : ℤ → ISite → Prop) : Prop :=
  ∀ t w, s < t → ¬ E t w → D t w = GI (D (t - 1)) w

/-! ## R4: the two references and the cluster count (Section 12 memory cover) -/

/-- A legal planar pattern: horizontally and vertically adjacent tiles match. -/
def Legal (θ : Plane → R) : Prop :=
  ∀ u, (θ u).1.E = (θ (u + (1, 0))).1.W ∧ (θ u).1.N = (θ (u + (0, 1))).1.S

/-- The transverse clone `ξ_θ(u, P) = θ(u)`. -/
def clone (θ : Plane → R) : ISite → Option R := fun w => some (θ w.1)

/-- A provider whose five cardinal inputs carry a legal pattern retains its central tile. -/
theorem chkI_clone_inputs {θ : Plane → R} (hθ : Legal θ) {y : Plane → Option R} {u : Plane}
    (h : ∀ γ ∈ cardinal, y (u + γ) = some (θ (u + γ))) : chkI y u = some (θ u) := by
  rw [chkI_eq_some]
  have hw : u + (-1, 0) + (1, 0) = u := by ext <;> simp
  have hs : u + (0, -1) + (0, 1) = u := by ext <;> simp
  have h0 := h _ mem_cardinal_zero
  simp only [plane_add_zero] at h0
  refine ⟨h0, ⟨_, h _ mem_cardinal_e1, (hθ u).1⟩,
    ⟨_, h _ mem_cardinal_w1, ?_⟩, ⟨_, h _ mem_cardinal_e2, (hθ u).2⟩, ⟨_, h _ mem_cardinal_w2, ?_⟩⟩
  · have := (hθ (u + (-1, 0))).1
    rwa [hw] at this
  · have := (hθ (u + (0, -1))).2
    rwa [hs] at this

/-- A live output has at least `h` providers with a live central input. -/
theorem GI_live_centres {D : ISite → Option R} {w : ISite} {s : R} (h : GI D w = some s) :
    quorum ≤ (Finset.univ.filter fun π : Provider => D (w.1, w.2 + offset π) ≠ none).card := by
  refine (GI_eq_some_iff.1 h).trans (Finset.card_le_card fun π hπ => ?_)
  rw [Finset.mem_filter] at hπ ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  have := (chkI_eq_some.1 hπ.2).1
  simp only at this
  rw [this]
  exact Option.some_ne_none _

/-- A wrong output at a clone reference: more than `K` providers have a wrong cardinal input
("if at most `K` checked providers were different from `θ(u)`, the other `q - K = h` would force
the correct output"). -/
theorem card_bad_of_ne_clone {θ : Plane → R} (hθ : Legal θ) {D : ISite → Option R} {w : ISite}
    (h : GI D w ≠ some (θ w.1)) :
    K < (Finset.univ.filter fun π : Provider => ∃ γ ∈ cardinal,
      D (w.1 + γ, w.2 + offset π) ≠ some (θ (w.1 + γ))).card := by
  classical
  by_contra hle
  push Not at hle
  apply h
  rw [GI_eq_some_iff]
  have hsub : (Finset.univ.filter fun π : Provider => ¬ ∃ γ ∈ cardinal,
      D (w.1 + γ, w.2 + offset π) ≠ some (θ (w.1 + γ))) ⊆
      (Finset.univ.filter fun π : Provider =>
        chkI (fun u => D (u, w.2 + offset π)) w.1 = some (θ w.1)) := by
    intro π hπ
    rw [Finset.mem_filter] at hπ ⊢
    refine ⟨Finset.mem_univ _, chkI_clone_inputs hθ fun γ hγ => ?_⟩
    by_contra hne
    exact hπ.2 ⟨γ, hγ, hne⟩
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Provider))
    (fun π : Provider => ∃ γ ∈ cardinal, D (w.1 + γ, w.2 + offset π) ≠ some (θ (w.1 + γ)))
  rw [Finset.card_univ, card_Provider] at hc
  have := Finset.card_le_card hsub
  unfold votesI
  simp only [q, K, quorum] at hc hle ⊢
  omega

open Classical in
/-- **The cluster count**: more than `K` providers with a marked Moore parent force marked parents
in two distinct clusters (each cluster has `K` providers). -/
theorem twoCl_of_card {M : ISite → Prop} {w : ISite}
    (h : K < (Finset.univ.filter fun π : Provider => FLD.Geometry.MarkedAt M w π).card) :
    FLD.Geometry.TwoCl M w := by
  classical
  obtain ⟨π0, hπ0⟩ : ∃ π, FLD.Geometry.MarkedAt M w π := by
    by_contra hc
    push Not at hc
    have : (Finset.univ.filter fun π : Provider => FLD.Geometry.MarkedAt M w π) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun π _ => hc π
    rw [this] at h
    simp at h
  by_contra hc
  have hone : ∀ π, FLD.Geometry.MarkedAt M w π → π.1 = π0.1 := by
    intro π hπ
    by_contra hne
    exact hc ⟨π, π0, hne, hπ, hπ0⟩
  have := Finset.card_le_card (s := Finset.univ.filter fun π : Provider => FLD.Geometry.MarkedAt M w π)
    (t := Finset.univ.filter fun π : Provider => π.1 = π0.1) fun π hπ =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hone π (Finset.mem_filter.1 hπ).2⟩
  rw [FLD.Geometry.card_cluster] at this
  omega

end FLD.Rule
