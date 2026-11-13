/-
Three-box ordinary geometry and the least finitary two-sided marked closure.
ADAPT: UND.Raw ordinary graph and UND.Coh finite-past closure; their concrete
five-cluster types are not reused. Provider and offset are FLD's statement data.
-/
import ForgettingLower.Constants
import UncomputableNoiseDiagram.Contour.Counting

set_option autoImplicit false

noncomputable section

namespace FLD.Geometry

open FNE (Plane box)
open FNE.EdgeCount

abbrev ISite := Plane × (Fin 2 → ℤ)

theorem card_Provider : Fintype.card Provider = q := by
  simp [Provider, q, K]

/-- Space-time points `((u, P), t)`. -/
abbrev Pt := ISite × ℤ

/-- The ordinary (data-checker) parent of `x` through the provider `π` at the planar displacement
`μ`: `((u + μ, P + s_π), t - 1)`. -/
def par (x : Pt) (π : Provider) (μ : Plane) : Pt := ((x.1.1 + μ, x.1.2 + offset π), x.2 - 1)

/-- The inverse of `par`. -/
def chi (x : Pt) (π : Provider) (μ : Plane) : Pt := ((x.1.1 - μ, x.1.2 - offset π), x.2 + 1)

theorem chi_par (x : Pt) (π : Provider) (μ : Plane) : chi (par x π μ) π μ = x := by
  obtain ⟨⟨u, P⟩, t⟩ := x
  simp [chi, par]

theorem par_time (x : Pt) (π : Provider) (μ : Plane) : (par x π μ).2 = x.2 - 1 := rfl

theorem par_ne (x : Pt) (π : Provider) (μ : Plane) : par x π μ ≠ x := by
  intro h
  have := congrArg Prod.snd h
  rw [par_time] at this
  omega

/-- One backward ordinary dependency step `w ↦ w'` (a Moore planar displacement and one checked
provider). -/
def OrdStep (w w' : ISite) : Prop := ∃ μ ∈ box 1, ∃ π : Provider, w' = (w.1 + μ, w.2 + offset π)

/-- The graph of ordinary steps, both directions. -/
def nbr (x : Pt) : Finset Pt :=
  (box 1 ×ˢ (Finset.univ : Finset Provider)).image (fun p => par x p.2 p.1) ∪
    (box 1 ×ˢ (Finset.univ : Finset Provider)).image (fun p => chi x p.2 p.1)

theorem card_box_one : (box 1).card = 9 := by
  simp [FNE.box]

/-- The graph has degree at most `18q`. -/
theorem card_nbr_le (x : Pt) : (nbr x).card ≤ 18 * q := by
  have h : (box 1 ×ˢ (Finset.univ : Finset Provider)).card = 9 * q := by
    rw [Finset.card_product, card_box_one, Finset.card_univ, card_Provider]
  calc (nbr x).card ≤ _ + _ := Finset.card_union_le _ _
    _ ≤ 9 * q + 9 * q :=
        Nat.add_le_add (Finset.card_image_le.trans h.le) (Finset.card_image_le.trans h.le)
    _ = 18 * q := by ring

theorem par_mem_nbr (x : Pt) (π : Provider) {μ : Plane} (hμ : μ ∈ box 1) : par x π μ ∈ nbr x :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(μ, π), Finset.mem_product.mpr
    ⟨hμ, Finset.mem_univ _⟩, rfl⟩)

theorem mem_nbr_par (x : Pt) (π : Provider) {μ : Plane} (hμ : μ ∈ box 1) : x ∈ nbr (par x π μ) :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(μ, π), Finset.mem_product.mpr
    ⟨hμ, Finset.mem_univ _⟩, chi_par x π μ⟩)

/-- An edge `{x, par x π μ}` lies in the graph. -/
theorem inGraph_par {x : Pt} {π : Provider} {μ : Plane} (hμ : μ ∈ box 1) :
    ∀ a b, s(a, b) = s(x, par x π μ) → b ∈ nbr a := by
  intro a b h
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact par_mem_nbr _ _ hμ
  · exact mem_nbr_par _ _ hμ

theorem not_isDiag_par (x : Pt) (π : Provider) (μ : Plane) : ¬ (s(x, par x π μ)).IsDiag := by
  rw [Sym2.mk_isDiag_iff]
  exact fun h => par_ne x π μ h.symm

/-- A provider has at least one marked logical input. -/
def MarkedAt (M : ISite → Prop) (w : ISite) (π : Provider) : Prop :=
  ∃ μ ∈ box 1, M (w.1 + μ, w.2 + offset π)

/-- Two marked ordinary parents in different boxes. -/
def TwoCl (M : ISite → Prop) (w : ISite) : Prop :=
  ∃ π π' : Provider, π.1 ≠ π'.1 ∧ MarkedAt M w π ∧ MarkedAt M w π'

/-- Closure under flags and two distinct supporting clusters. -/
def MClosed (E M : ℤ → ISite → Prop) : Prop :=
  ∀ t w, E t w ∨ TwoCl (M (t - 1)) w → M t w

/-- `𝓜^{t₀}` at time `t₀ + n`: empty at `t₀`; then each replacement flag and each site having a
marked Moore parent in two distinct provider clusters. -/
def markedFrom (E : ℤ → ISite → Prop) (t0 : ℤ) : ℕ → ISite → Prop
  | 0 => fun _ => False
  | n + 1 => fun w => E (t0 + (n + 1 : ℕ)) w ∨ TwoCl (markedFrom E t0 n) w

/-- **`𝓜`**: the increasing limit of `𝓜^{t₀}` as `t₀ → -∞` (membership has a finite derivation;
it is determined by the flags alone). -/
def marked (E : ℤ → ISite → Prop) (t : ℤ) (w : ISite) : Prop :=
  ∃ n : ℕ, markedFrom E (t - n) n w

theorem markedAt_mono {M M' : ISite → Prop} (h : ∀ w, M w → M' w) {w : ISite} {π : Provider}
    (hm : MarkedAt M w π) : MarkedAt M' w π := by
  obtain ⟨μ, hμ, hm⟩ := hm
  exact ⟨μ, hμ, h _ hm⟩

theorem twoCl_mono {M M' : ISite → Prop} (h : ∀ w, M w → M' w) {w : ISite} (hm : TwoCl M w) :
    TwoCl M' w := by
  obtain ⟨π, π', hne, h1, h2⟩ := hm
  exact ⟨π, π', hne, markedAt_mono h h1, markedAt_mono h h2⟩

/-- An earlier start marks more: `𝓜^{t₀} ⊆ 𝓜^{t₀ - 1}`. -/
theorem markedFrom_mono (E : ℤ → ISite → Prop) (t0 : ℤ) (n : ℕ) :
    ∀ w, markedFrom E t0 n w → markedFrom E (t0 - 1) (n + 1) w := by
  induction n with
  | zero => intro w h; exact h.elim
  | succ n ih =>
    intro w h
    rcases h with h | h
    · left
      have e : t0 - 1 + ((n + 1 + 1 : ℕ) : ℤ) = t0 + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e]; exact h
    · exact Or.inr (twoCl_mono ih h)

theorem markedFrom_mono' (E : ℤ → ISite → Prop) (t0 : ℤ) (n k : ℕ) (w : ISite)
    (h : markedFrom E t0 n w) : markedFrom E (t0 - k) (n + k) w := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have := markedFrom_mono E (t0 - k) (n + k) w ih
    rwa [show t0 - (k : ℤ) - 1 = t0 - ((k + 1 : ℕ) : ℤ) by push_cast; ring,
      show n + k + 1 = n + (k + 1) by ring] at this

/-- The finitary two-sided marked set is closed under flags and distinct-box support. -/
theorem marked_closed (E : ℤ → ISite → Prop) : MClosed E (marked E) := by
  intro t w h
  rcases h with h | h
  · refine ⟨1, Or.inl ?_⟩
    rwa [show t - ((1 : ℕ) : ℤ) + ((0 + 1 : ℕ) : ℤ) = t by push_cast; ring]
  · obtain ⟨π, π', hne, ⟨μ, hμ, n1, h1⟩, ⟨μ', hμ', n2, h2⟩⟩ := h
    set N := max n1 n2
    have g1 := markedFrom_mono' E _ _ (N - n1) _ h1
    have g2 := markedFrom_mono' E _ _ (N - n2) _ h2
    rw [show t - 1 - (n1 : ℤ) - ((N - n1 : ℕ) : ℤ) = t - 1 - N by omega,
      show n1 + (N - n1) = N by omega] at g1
    rw [show t - 1 - (n2 : ℤ) - ((N - n2 : ℕ) : ℤ) = t - 1 - N by omega,
      show n2 + (N - n2) = N by omega] at g2
    refine ⟨N + 1, Or.inr ⟨π, π', hne, ⟨μ, hμ, ?_⟩, ⟨μ', hμ', ?_⟩⟩⟩
    · rwa [show t - ((N + 1 : ℕ) : ℤ) = t - 1 - N by push_cast; ring]
    · rwa [show t - ((N + 1 : ℕ) : ℤ) = t - 1 - N by push_cast; ring]

/-- The finite-past closure lies in every set closed under the two rules. -/
theorem markedFrom_le {E M : ℤ → ISite → Prop} (hM : MClosed E M)
    (t0 : ℤ) (n : ℕ) : ∀ w, markedFrom E t0 n w → M (t0 + n) w := by
  induction n with
  | zero => intro w h; exact h.elim
  | succ n ih =>
    intro w h
    apply hM
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (twoCl_mono (by
        intro v hv
        have hi := ih v hv
        convert hi using 1; push_cast; ring) h)

/-- The two-sided marked set is the least closed set containing the flags. -/
theorem marked_le {E M : ℤ → ISite → Prop} (hM : MClosed E M)
    {t : ℤ} {w : ISite} (h : marked E t w) : M t w := by
  obtain ⟨n, hn⟩ := h
  have hi := markedFrom_le hM (t - n) n w hn
  simpa using hi

/-- Membership unfolds into a flag or two marked ordinary parents. -/
theorem marked_iff {E : ℤ → ISite → Prop} {t : ℤ} {w : ISite} :
    marked E t w ↔ E t w ∨ TwoCl (marked E (t - 1)) w := by
  refine ⟨?_, marked_closed E t w⟩
  rintro ⟨n, hn⟩
  cases n with
  | zero => exact hn.elim
  | succ n =>
    rcases hn with hn | hn
    · exact Or.inl (by simpa using hn)
    · right
      apply twoCl_mono (M := markedFrom E (t - (n + 1 : ℕ)) n) _ hn
      intro v hv
      exact ⟨n, by convert hv using 1; push_cast; ring⟩

/-- Auxiliary marked-parent event H; its definition does not alter the closure. -/
def H (E : ℤ → ISite → Prop) (x : Pt) : Prop :=
  ∃ μ ∈ box 1, ∃ π : Provider, marked E (x.2 - 1) (par x π μ).1

theorem not_flag_of_not_marked {E : ℤ → ISite → Prop} {t : ℤ} {w : ISite}
    (h : ¬ marked E t w) : ¬ E t w :=
  fun he => h (marked_closed E t w (Or.inl he))

/-- An unmarked vertex can have affected offsets in at most one cluster. -/
theorem one_cluster {E : ℤ → ISite → Prop} {t : ℤ} {w : ISite}
    (h : ¬ marked E t w) :
    ∃ c : Option (Fin 2), ∀ π, MarkedAt (marked E (t - 1)) w π → π.1 = c := by
  classical
  by_cases hex : ∃ π, MarkedAt (marked E (t - 1)) w π
  · obtain ⟨π0, h0⟩ := hex
    refine ⟨π0.1, fun π hπ => ?_⟩
    by_contra hne
    exact h (marked_closed E t w (Or.inr ⟨π, π0, hne, hπ, h0⟩))
  · exact ⟨none, fun π hπ => absurd ⟨π, hπ⟩ hex⟩

open Classical in
theorem card_cluster (c : Option (Fin 2)) :
    (Finset.univ.filter fun π : Provider => π.1 = c).card = K := by
  have e : (Finset.univ.filter fun π : Provider => π.1 = c) = {c} ×ˢ Finset.univ := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, and_true]
  rw [e, Finset.card_product, Finset.card_singleton, Finset.card_univ]
  simp [K]

open Classical in
/-- The precise one-box exclusion budget K=256. -/
theorem card_marked_le {E : ℤ → ISite → Prop} {t : ℤ} {w : ISite}
    (h : ¬ marked E t w) :
    (Finset.univ.filter fun π => MarkedAt (marked E (t - 1)) w π).card ≤ K := by
  obtain ⟨c, hc⟩ := one_cluster h
  rw [← card_cluster c]
  exact Finset.card_le_card fun π hπ =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hc π (Finset.mem_filter.1 hπ).2⟩

end FLD.Geometry