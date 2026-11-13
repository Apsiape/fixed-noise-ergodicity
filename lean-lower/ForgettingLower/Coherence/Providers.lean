/- Clean successful providers, retaining the full Moore contamination neighbourhood. -/
import ForgettingLower.Rule.Bridge

set_option autoImplicit false

noncomputable section
namespace FLD.Coh
open FLD.Geometry FLD.Rule Classical
open FNE (Plane WangSet box)
variable {R : WangSet}

/-- An unmarked live reading of the tile `a` at `(w, t)`. -/
def UL (D : ℤ → ISite → Option R) (M : ℤ → ISite → Prop) (t : ℤ) (w : ISite) (a : R) : Prop :=
  ¬ M t w ∧ D t w = some a

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
  simp only [cardinal, FNR.cardinal, Finset.mem_insert, Finset.mem_singleton] at hγ
  obtain ⟨h0, ⟨b1, e1, -⟩, ⟨b2, e2, -⟩, ⟨b3, e3, -⟩, ⟨b4, e4, -⟩⟩ := hk
  rcases hγ with rfl | rfl | rfl | rfl | rfl
  · exact ⟨c, by rw [plane_add_zero]; exact h0⟩
  · exact ⟨b1, e1⟩
  · exact ⟨b2, e2⟩
  · exact ⟨b3, e3⟩
  · exact ⟨b4, e4⟩

/-- A good provider (successful, no marked Moore input) supplies an unmarked live reading of the
same tile one step earlier. -/
theorem ul_of_good {t : ℤ} {u : Plane} {P : Fin 2 → ℤ} {π : Provider} {a : R}
    (hchk : chkI (fun v => D (t - 1) (v, P + offset π)) u = some a)
    (hm : ¬ MarkedAt (M (t - 1)) (u, P) π) : UL D M (t - 1) (u, P + offset π) a :=
  ⟨fun hM' => hm ⟨0, by simp [box], by simpa using hM'⟩, (chkI_eq_some.1 hchk).1⟩

/-- A good provider supplies unmarked live readings at all five cardinal inputs. -/
theorem ul_nbr_of_good {t : ℤ} {u : Plane} {P : Fin 2 → ℤ} {π : Provider} {a : R}
    (hchk : chkI (fun v => D (t - 1) (v, P + offset π)) u = some a)
    (hm : ¬ MarkedAt (M (t - 1)) (u, P) π) {γ : Plane} (hγ : γ ∈ cardinal) :
    ∃ b, UL D M (t - 1) (u + γ, P + offset π) b := by
  obtain ⟨b, hb⟩ := keepsI_live (chkI_eq_some.1 hchk) hγ
  exact ⟨b, fun hM' => hm ⟨γ, cardinal_sub_box γ hγ, hM'⟩, hb⟩


/-- A complete flag trajectory has no initial-time boundary. -/
def IsHistory (D : ℤ → ISite → Option R) (E : ℤ → ISite → Prop) : Prop :=
  ∀ t w, ¬ E t w → D t w = GI (D (t - 1)) w

theorem IsHistory.isTraj {D : ℤ → ISite → Option R} {E : ℤ → ISite → Prop}
    (hD : IsHistory D E) (s : ℤ) : IsTraj s D E := fun t w _ => hD t w

theorem isHistory_of_complete {ω : (natCA R).Noise₂} {X : ℤ → (natCA R).Config}
    (hX : (natCA R).IsComplete ω X) : IsHistory (fun t => dec (X t)) (flagsOf ω) := by
  intro t w hE
  exact isTraj_of_complete hX (t - 1) t w (by omega) hE

/-- A live unmarked output has at least quorum-K = K clean successful providers. -/
theorem card_good_ge {D : ℤ → ISite → Option R} {E : ℤ → ISite → Prop}
    (hD : IsHistory D E) {t : ℤ} {w : ISite} {a : R}
    (h : UL D (marked E) t w a) :
    K ≤ (Finset.univ.filter fun π : Provider =>
      chkI (fun v => D (t - 1) (v, w.2 + offset π)) w.1 = some a ∧
        ¬ MarkedAt (marked E (t - 1)) w π).card := by
  classical
  have hv := GI_eq_some_iff.1 (h.gi (hD.isTraj (t - 1)) (marked_closed E) (by omega))
  have hm := card_marked_le h.1
  let S : Finset Provider := Finset.univ.filter fun π =>
    chkI (fun v => D (t - 1) (v, w.2 + offset π)) w.1 = some a
  have hc := Finset.card_filter_add_card_filter_not (s := S)
    (fun π => MarkedAt (marked E (t - 1)) w π)
  have hle : (S.filter fun π => MarkedAt (marked E (t - 1)) w π).card ≤ K := by
    exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans hm
  have heq : (S.filter fun π => ¬ MarkedAt (marked E (t - 1)) w π) =
      Finset.univ.filter (fun π : Provider =>
        chkI (fun v => D (t - 1) (v, w.2 + offset π)) w.1 = some a ∧
          ¬ MarkedAt (marked E (t - 1)) w π) := by ext π; simp [S]
  rw [heq] at hc
  change quorum ≤ S.card at hv
  rw [Const.K_eq] at hm hle ⊢
  rw [Const.quorum_eq] at hv
  omega

/-- At least one clean successful provider exists, even at an H step. -/
theorem exists_good {D : ℤ → ISite → Option R} {E : ℤ → ISite → Prop}
    (hD : IsHistory D E) {t : ℤ} {w : ISite} {a : R}
    (h : UL D (marked E) t w a) :
    ∃ π : Provider, chkI (fun v => D (t - 1) (v, w.2 + offset π)) w.1 = some a ∧
      ¬ MarkedAt (marked E (t - 1)) w π := by
  classical
  have hc := card_good_ge hD h
  have hp : 0 < (Finset.univ.filter fun π : Provider =>
      chkI (fun v => D (t - 1) (v, w.2 + offset π)) w.1 = some a ∧
        ¬ MarkedAt (marked E (t - 1)) w π).card := lt_of_lt_of_le (by norm_num [K] : 0 < K) hc
  obtain ⟨π, hπ⟩ := Finset.card_pos.mp hp
  exact ⟨π, (Finset.mem_filter.mp hπ).2⟩

/-- No H at a root means that every provider is clean on all Moore inputs. -/
theorem clean_of_not_H {E : ℤ → ISite → Prop} {t : ℤ} {w : ISite}
    (h : ¬ H E (w, t)) (π : Provider) : ¬ MarkedAt (marked E (t - 1)) w π := by
  rintro ⟨μ, hμ, hm⟩
  exact h ⟨μ, hμ, π, hm⟩

/-- A clean checker supplies the entire unmarked live cardinal star one time earlier. -/
theorem coh_back {D : ℤ → ISite → Option R} {E : ℤ → ISite → Prop}
    (hD : IsHistory D E) {t : ℤ} {u : Plane} {P : Fin 2 → ℤ} {a : R}
    (h : UL D (marked E) t (u, P) a) :
    ∃ P', UL D (marked E) (t - 1) (u, P') a ∧
      ∀ γ ∈ cardinal, ∃ b, UL D (marked E) (t - 1) (u + γ, P') b := by
  obtain ⟨π, hc, hm⟩ := exists_good hD h
  exact ⟨P + offset π, ul_of_good hc hm, fun γ hγ => ul_nbr_of_good hc hm hγ⟩

end FLD.Coh
