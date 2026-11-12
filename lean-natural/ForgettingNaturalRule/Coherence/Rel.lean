/-
# Finite-age coherence (Lemmas `nw:budget`, `nw:same`, `nw:neighbours`) (nodes C1–C4)

Paper. Lemma `nw:budget`: "An unmarked vertex is unflagged. Among its provider offsets `a ∈ S`, at
most `K` have any marked Moore parent." Section "Successful and unaffected providers": "Call a
provider good if it is successful and unaffected by marked inputs. At least `h - K = 3K`
providers are good. A good provider supplies five unmarked live cardinal inputs one time earlier,
with central letter `s` and matched central edges."
Lemma `nw:same`: "two unmarked live readings at `(u,P,t)` and `(u,Q,t)` have the same tile whenever
`d = ‖Q - P‖₁ ≤ t`" (induction on `d`, the injective unit-shift pairing, surplus
`(75/16 - 4)K > 0`). Lemma `nw:neighbours`: "Unmarked live readings at `(u,P,t)` and
`(u+γ,Q,t)` have matching shared edges if `t ≥ ‖Q-P‖₁ + 1`" (base: the successful-provider sets
overlap in `2h - q = 3K` offsets).

Formalization (deterministic, for one trajectory `D` of `G_R` from time `s` with flags `E`, and any
marked set `M` closed under the two rules (`UND.Coh.MClosed`, REUSE); ages are `t - s`):
* REUSE from the noise-diagram core (`Contour/Coherence.lean`): `MarkedAt`, `TwoCl`, `MClosed`,
  `card_marked_le` (Lemma `nw:budget`), the pairing `PSrc`, `pHi`, `pLo`, `exists_pair`
  (`|Bad₁| + |Bad₂| < 5·15·16³`), `provOff_pair`, the separation `sep`, `sep_zero`, `sep_step`;
* `UL` (an unmarked live reading), `UL.gi`, `ul_of_good`, `ul_nbr_of_good` (a good provider);
* **`coh_rel`**: the induction on the transverse separation for the displacements `0`, `e₁`, `e₂`
  (`Rel`), under `s + d < t` (one unit of age beyond the paper's `d ≤ t` for equal planar sites;
  immaterial for the core, which uses complete trajectories);
* **`coh_back`**: `V_t + Γ ⊆ V_{t-1}` with the label persisting at the centre.
-/
import ForgettingNaturalRule.Rule.Local

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace FNR.Coh

open UND.Rule (ISite Prov provOff card_Prov)
open UND.Coh (MClosed MarkedAt TwoCl sep sep_zero sep_step pHi pLo pHi_injective pLo_injective
  provOff_pair exists_pair card_marked_le)
open FNR.Rule
open FNE (Plane WangSet box)

variable {R : WangSet}

/-- An unmarked live reading of the tile `a` at `(w, t)`. -/
def UL (D : ℤ → ISite → Option R) (M : ℤ → ISite → Prop) (t : ℤ) (w : ISite) (a : R) : Prop :=
  ¬ M t w ∧ D t w = some a

/-- The planar displacements compared by the induction: `0`, `e₁`, `e₂`. -/
def dirs : Finset Plane := {(0, 0), (1, 0), (0, 1)}

/-- The coherence relation at the displacement `γ`: equal tiles for `γ = 0`, the shared vertical
edge for `γ = e₁` (`a'` east of `a`), the shared horizontal edge for `γ = e₂` (`a'` north of
`a`). -/
def Rel (γ : Plane) (a a' : R) : Prop :=
  (γ = (0, 0) → a = a') ∧ (γ = (1, 0) → a.1.E = a'.1.W) ∧ (γ = (0, 1) → a.1.N = a'.1.S)

variable {s : ℤ} {D : ℤ → ISite → Option R} {E M : ℤ → ISite → Prop}

/-- An unmarked live reading at a positive age is an ordinary `G_R` output. -/
theorem UL.gi (hX : IsTraj s D E) (hM : MClosed E M) {t : ℤ} {w : ISite} {a : R}
    (hs : s < t) (h : UL D M t w a) : GI (D (t - 1)) w = some a := by
  have hE : ¬ E t w := fun hE => h.1 (hM t w (Or.inl hE))
  rw [← hX t w hs hE]
  exact h.2

/-- A kept centre has live cardinal neighbours. -/
theorem keepsI_live {y : Plane → Option R} {u : Plane} {c : R} (hk : KeepsI y u c) {γ : Plane}
    (hγ : γ ∈ cardinal) : ∃ b, y (u + γ) = some b := by
  simp only [cardinal, Finset.mem_insert, Finset.mem_singleton] at hγ
  obtain ⟨h0, ⟨b1, e1, -⟩, ⟨b2, e2, -⟩, ⟨b3, e3, -⟩, ⟨b4, e4, -⟩⟩ := hk
  rcases hγ with rfl | rfl | rfl | rfl | rfl
  · exact ⟨c, by rw [plane_add_zero]; exact h0⟩
  · exact ⟨b1, e1⟩
  · exact ⟨b2, e2⟩
  · exact ⟨b3, e3⟩
  · exact ⟨b4, e4⟩

/-- A good provider (successful, no marked Moore input) supplies an unmarked live reading of the
same tile one step earlier. -/
theorem ul_of_good {t : ℤ} {u : Plane} {P : Fin 4 → ℤ} {π : Prov} {a : R}
    (hchk : chkI (fun v => D (t - 1) (v, P + provOff π)) u = some a)
    (hm : ¬ MarkedAt (M (t - 1)) (u, P) π) : UL D M (t - 1) (u, P + provOff π) a :=
  ⟨fun hM' => hm ⟨0, by simp [box], by simpa using hM'⟩, (chkI_eq_some.1 hchk).1⟩

/-- A good provider supplies unmarked live readings at all five cardinal inputs. -/
theorem ul_nbr_of_good {t : ℤ} {u : Plane} {P : Fin 4 → ℤ} {π : Prov} {a : R}
    (hchk : chkI (fun v => D (t - 1) (v, P + provOff π)) u = some a)
    (hm : ¬ MarkedAt (M (t - 1)) (u, P) π) {γ : Plane} (hγ : γ ∈ cardinal) :
    ∃ b, UL D M (t - 1) (u + γ, P + provOff π) b := by
  obtain ⟨b, hb⟩ := keepsI_live (chkI_eq_some.1 hchk) hγ
  exact ⟨b, fun hM' => hm ⟨γ, cardinal_sub_box γ hγ, hM'⟩, hb⟩

/-- **The coherence induction** (Lemmas `nw:same`, `nw:neighbours`) on the transverse separation
`n = ‖P' - P‖₁`: unmarked live readings at `(u, P, t)` and `(u + γ, P', t)`, `γ ∈ {0, e₁, e₂}`,
are related by `Rel γ` as soon as `s + n < t`. -/
theorem coh_rel (hX : IsTraj s D E) (hM : MClosed E M) (n : ℕ) :
    ∀ (t : ℤ) (u : Plane) (P P' : Fin 4 → ℤ) (γ : Plane) (a a' : R), γ ∈ dirs →
      sep P P' = n → s + n < t → UL D M t (u, P) a → UL D M t (u + γ, P') a' → Rel γ a a' := by
  classical
  induction n with
  | zero =>
    intro t u P P' γ a a' hγ hsep ht h h'
    obtain rfl := sep_zero hsep
    simp only [dirs, Finset.mem_insert, Finset.mem_singleton] at hγ
    rcases hγ with rfl | hγ | hγ
    · refine ⟨fun _ => ?_, fun e => absurd e (by decide), fun e => absurd e (by decide)⟩
      rw [plane_add_zero] at h'
      exact Option.some_injective _ (h.2.symm.trans h'.2)
    all_goals
      have hA := GI_eq_some_iff.1 (h.gi hX hM (by omega))
      have hA' := GI_eq_some_iff.1 (h'.gi hX hM (by omega))
      unfold votesI at hA hA'
      dsimp only at hA hA'
      have hq := UND.Param.q_lt_two_h
      obtain ⟨π, hπ⟩ := Finset.inter_nonempty_of_card_lt_card_add_card (s := Finset.univ)
        (Finset.subset_univ _) (Finset.subset_univ _)
        (by rw [Finset.card_univ, card_Prov]; omega : Finset.univ.card <
          (Finset.univ.filter fun π : Prov =>
            chkI (fun v => D (t - 1) (v, P + provOff π)) u = some a).card +
          (Finset.univ.filter fun π : Prov =>
            chkI (fun v => D (t - 1) (v, P + provOff π)) (u + γ) = some a').card)
      rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hπ
      obtain ⟨⟨-, c1⟩, ⟨-, c2⟩⟩ := hπ
      have k1 := chkI_eq_some.1 c1
      have k2 := (chkI_eq_some.1 c2).1
      subst hγ
    · obtain ⟨b, hb, hab⟩ := k1.2.1
      have hba : b = a' := Option.some_injective _ (hb.symm.trans k2)
      subst hba
      exact ⟨fun e => absurd e (by decide), fun _ => hab, fun e => absurd e (by decide)⟩
    · obtain ⟨b, hb, hab⟩ := k1.2.2.2.1
      have hba : b = a' := Option.some_injective _ (hb.symm.trans k2)
      subst hba
      exact ⟨fun e => absurd e (by decide), fun e => absurd e (by decide), fun _ => hab⟩
  | succ n ih =>
    intro t u P P' γ a a' hγ hsep ht h h'
    have hne : P ≠ P' := by
      rintro rfl
      simp [sep] at hsep
    obtain ⟨j, hj⟩ : ∃ j, P j ≠ P' j := by
      by_contra hc
      push Not at hc
      exact hne (funext hc)
    have hA := h.gi hX hM (by omega)
    have hA' := h'.gi hX hM (by omega)
    have hf1 := card_failed_le hA
    have hf2 := card_failed_le hA'
    dsimp only at hf1 hf2
    have hm1 := card_marked_le hM h.1
    have hm2 := card_marked_le hM h'.1
    set Bad1 := (Finset.univ.filter fun π : Prov =>
        ¬ chkI (fun v => D (t - 1) (v, P + provOff π)) u = some a) ∪
      (Finset.univ.filter fun π => MarkedAt (M (t - 1)) (u, P) π) with hB1
    set Bad2 := (Finset.univ.filter fun π : Prov =>
        ¬ chkI (fun v => D (t - 1) (v, P' + provOff π)) (u + γ) = some a') ∪
      (Finset.univ.filter fun π => MarkedAt (M (t - 1)) (u + γ, P') π) with hB2
    have hc1 : Bad1.card ≤ 2 * UND.Param.K :=
      (Finset.card_union_le _ _).trans (by omega)
    have hc2 : Bad2.card ≤ 2 * UND.Param.K :=
      (Finset.card_union_le _ _).trans (by omega)
    have hK : UND.Param.K = 65536 := by norm_num [UND.Param.K]
    have hcard : Bad1.card + Bad2.card < 5 * 15 * 16 ^ 3 := by omega
    have good1 : ∀ π, π ∉ Bad1 → UL D M (t - 1) (u, P + provOff π) a := fun π hπ => by
      simp only [hB1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        not_or, not_not] at hπ
      exact ul_of_good hπ.1 hπ.2
    have good2 : ∀ π, π ∉ Bad2 → UL D M (t - 1) (u + γ, P' + provOff π) a' := fun π hπ => by
      simp only [hB2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        not_or, not_not] at hπ
      exact ul_of_good hπ.1 hπ.2
    by_cases hdir : P j < P' j
    · obtain ⟨σ, hσ1, hσ2⟩ := exists_pair (pHi j) (pLo j) (pHi_injective j) (pLo_injective j)
        Bad1 Bad2 hcard
      have hstep := sep_step (P := P) (P' := P') (provOff (pHi j σ)) (provOff (pLo j σ))
        (fun i => by
          rw [provOff_pair j σ i, Int.sign_eq_one_of_pos (by omega)]
          split_ifs <;> ring) hj
      exact ih (t - 1) u _ _ γ a a' hγ (by omega) (by omega) (good1 _ hσ1) (good2 _ hσ2)
    · obtain ⟨σ, hσ1, hσ2⟩ := exists_pair (pLo j) (pHi j) (pLo_injective j) (pHi_injective j)
        Bad1 Bad2 hcard
      have hstep := sep_step (P := P) (P' := P') (provOff (pLo j σ)) (provOff (pHi j σ))
        (fun i => by
          rw [provOff_pair j σ i, Int.sign_eq_neg_one_of_neg (by omega)]
          split_ifs <;> ring) hj
      exact ih (t - 1) u _ _ γ a a' hγ (by omega) (by omega) (good1 _ hσ1) (good2 _ hσ2)

/-- **`V_t + Γ ⊆ V_{t-1}`**, with the label persisting at the centre: an unmarked live reading at a
positive age has a good provider, which supplies unmarked live readings at its five cardinal
inputs one step earlier, the central one carrying the same tile. -/
theorem coh_back (hX : IsTraj s D E) (hM : MClosed E M) {t : ℤ} {u : Plane} {P : Fin 4 → ℤ}
    {a : R} (hs : s < t) (h : UL D M t (u, P) a) :
    ∃ P', UL D M (t - 1) (u, P') a ∧ ∀ γ ∈ cardinal, ∃ b, UL D M (t - 1) (u + γ, P') b := by
  classical
  have hQ := GI_eq_some_iff.1 (h.gi hX hM hs)
  unfold votesI at hQ
  dsimp only at hQ
  have hm := card_marked_le hM h.1
  have hK : UND.Param.h = 4 * UND.Param.K := rfl
  have hK0 : 0 < UND.Param.K := by norm_num [UND.Param.K]
  obtain ⟨π, hπ1, hπ2⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega :
    (Finset.univ.filter fun π => MarkedAt (M (t - 1)) (u, P) π).card <
      (Finset.univ.filter fun π : Prov =>
        chkI (fun v => D (t - 1) (v, P + provOff π)) u = some a).card)
  rw [Finset.mem_filter] at hπ1
  have hπ2' : ¬ MarkedAt (M (t - 1)) (u, P) π := fun hc =>
    hπ2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩)
  exact ⟨P + provOff π, ul_of_good hπ1.2 hπ2', fun γ hγ => ul_nbr_of_good hπ1.2 hπ2' hγ⟩

end FNR.Coh
