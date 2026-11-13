/-
Three balanced potentials and the three-charge grouped support system.
ADAPT: UND.Raw.sys, with actual FLD providers; new exact gains 130 and -350.
-/
import ForgettingLower.Geometry.Marked

set_option autoImplicit false

noncomputable section

namespace FLD.Geometry

open FNE (Plane box)
open UND.Contour
section System

variable (E : ℤ → ISite → Prop) (t0 : ℤ)

/-- Membership in `𝓜^{t₀}` of a space-time point. -/
def MF (x : Pt) : Prop := t0 ≤ x.2 ∧ markedFrom E t0 (x.2 - t0).toNat x.1

/-- An admissible choice of two marked parents in distinct provider clusters. -/
def PGood (x : Pt) (d : (Provider × Plane) × (Provider × Plane)) : Prop :=
  d.1.1.1 ≠ d.2.1.1 ∧ d.1.2 ∈ box 1 ∧ d.2.2 ∈ box 1 ∧
    MF E t0 (par x d.1.1 d.1.2) ∧ MF E t0 (par x d.2.1 d.2.2)

/-- The chosen parents. -/
def pd (x : Pt) : (Provider × Plane) × (Provider × Plane) := Classical.epsilon (PGood E t0 x)

/-- The selected parent `b` (provider and planar displacement). -/
def sel (x : Pt) (b : Bool) : Provider × Plane := if b then (pd E t0 x).1 else (pd E t0 x).2

/-- Binary vertices: marked non-flag points. -/
def NFm (x : Pt) : Prop := MF E t0 x ∧ ¬ E x.2 x.1

variable {E t0}

theorem MF.time_lt {x : Pt} (h : MF E t0 x) : t0 < x.2 := by
  obtain ⟨h1, h2⟩ := h
  by_contra hc
  have e : (x.2 - t0).toNat = 0 := by omega
  rw [e] at h2
  exact h2

theorem mf_par {x : Pt} {m : ℕ} (hm : (x.2 - t0).toNat = m + 1) {π : Provider} {μ : Plane}
    (h : markedFrom E t0 m (x.1.1 + μ, x.1.2 + offset π)) : MF E t0 (par x π μ) := by
  refine ⟨by rw [par_time]; omega, ?_⟩
  rw [par_time, show (x.2 - 1 - t0).toNat = m by omega]
  exact h

theorem exists_pgood {x : Pt} (h : NFm E t0 x) : ∃ d, PGood E t0 x d := by
  obtain ⟨⟨h1, h2⟩, hE⟩ := h
  have hlt := MF.time_lt ⟨h1, h2⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (x.2 - t0).toNat = m + 1 := ⟨(x.2 - t0).toNat - 1, by omega⟩
  rw [hm] at h2
  rcases h2 with h2 | h2
  · exact absurd (by rwa [show t0 + ((m + 1 : ℕ) : ℤ) = x.2 by omega] at h2) hE
  · obtain ⟨π, π', hne, ⟨μ, hμ, hm1⟩, ⟨μ', hμ', hm2⟩⟩ := h2
    exact ⟨((π, μ), (π', μ')), hne, hμ, hμ', mf_par hm hm1, mf_par hm hm2⟩

theorem pd_spec {x : Pt} (h : NFm E t0 x) : PGood E t0 x (pd E t0 x) :=
  Classical.epsilon_spec (exists_pgood h)

theorem sel_box {x : Pt} (h : NFm E t0 x) (b : Bool) : (sel E t0 x b).2 ∈ box 1 := by
  have := pd_spec h
  cases b
  · exact this.2.2.1
  · exact this.2.1

theorem sel_mf {x : Pt} (h : NFm E t0 x) (b : Bool) :
    MF E t0 (par x (sel E t0 x b).1 (sel E t0 x b).2) := by
  have := pd_spec h
  cases b
  · exact this.2.2.2.2
  · exact this.2.2.2.1

theorem sel_ne {x : Pt} (h : NFm E t0 x) : (sel E t0 x true).1.1 ≠ (sel E t0 x false).1.1 :=
  (pd_spec h).1

variable (E t0)

/-- **The marked derivation as a grouped support graph** (Lemma 5.1's hypotheses for Lemma 5.2):
binary vertices are the marked non-flag points with their two selected marked parents in distinct
clusters, the good parent of charge `c` is one whose cluster is not `c`, there are no unary links,
and the terminal groups are singletons (`grp = id`). -/
def sys : GroupedSystem Pt (Option (Fin 2)) Pt where
  rk x := (x.2 - t0).toNat
  NF := NFm E t0
  UN _ := False
  not_UN_of_NF _ _ h := h
  sup x b := par x (sel E t0 x b).1 (sel E t0 x b).2
  un x := x
  good c x := decide ((sel E t0 x true).1.1 ≠ c)
  grp x := x
  rk_sup x b h := by
    have := MF.time_lt h.1
    show (x.2 - 1 - t0).toNat < (x.2 - t0).toNat
    omega
  rk_un _ h := h.elim

variable {E t0}

theorem sys_sup (x : Pt) (b : Bool) :
    (sys E t0).sup x b = par x (sel E t0 x b).1 (sel E t0 x b).2 := rfl

/-- The good parent of charge `c` lies in a cluster other than `c`. -/
theorem sel_good {x : Pt} (h : NFm E t0 x) (c : Option (Fin 2)) :
    (sel E t0 x ((sys E t0).good c x)).1.1 ≠ c := by
  show (sel E t0 x (decide ((sel E t0 x true).1.1 ≠ c))).1.1 ≠ c
  by_cases hc : (sel E t0 x true).1.1 = c
  · rw [decide_eq_false (not_not.mpr hc)]
    intro h'
    exact sel_ne h (hc.trans h'.symm)
  · rw [decide_eq_true hc]
    exact hc


/-- The three balanced potentials, independent of the logical coordinates. -/
def psi : Option (Fin 2) → Pt → ℤ
  | none, x => 3 * (x.1.2 0 + x.1.2 1) + 350 * x.2
  | some i, x => -3 * x.1.2 i - 175 * x.2

theorem psi_sum (x : Pt) : ∑ c, psi c x = 0 := by
  rw [Fintype.sum_option, Fin.sum_univ_two]
  simp only [psi]
  ring

/-- Every gain is at least -350; outside charge c's box it is at least 130. -/
theorem psi_par (c : Option (Fin 2)) (x : Pt) (π : Provider) (μ : Plane) :
    psi c x - 350 ≤ psi c (par x π μ) ∧
      (π.1 ≠ c → psi c x + 130 ≤ psi c (par x π μ)) := by
  rcases π with ⟨cl, o⟩
  have h0 : 0 ≤ ((o 0 : ℕ) : ℤ) ∧ ((o 0 : ℕ) : ℤ) ≤ 15 := by
    have := (o 0).isLt
    constructor <;> omega
  have h1 : 0 ≤ ((o 1 : ℕ) : ℤ) ∧ ((o 1 : ℕ) : ℤ) ≤ 15 := by
    have := (o 1).isLt
    constructor <;> omega
  rcases c with _ | i <;> rcases cl with _ | j
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp only [psi, par, offset, corner, Pi.add_apply]
  all_goals (norm_num; omega)

theorem isPotential_psi : (sys E t0).IsPotential psi 130 350 := by
  refine ⟨psi_sum, fun x c h => ?_, fun x b c _ => ?_, fun x c h => h.elim⟩
  · exact (psi_par c x _ _).2 (sel_good h c)
  · exact (psi_par c x _ _).1

end System
end FLD.Geometry