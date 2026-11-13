/-
# Section 3 (forgetting): `fgt:path`, `fgt:packing` and `thm:forgetting`

Printed Section 3 ("Bounded-width refutations give forgetting", source file `04-forgetting.tex`),
Sections 3.5 and 3.6.
* `discrepancy_path` (`fgt:path`): a discrepancy between the runs from `x` and from `⊥` at
  `(v, t)` is joined to time `0` by a path of discrepancies through non-events, each step to a
  site of `v + 𝒩`;
* `packing` (`fgt:packing`): after the refutation time, the contours of `lem:contour` placed along
  that path in disjoint time slabs give a connected set `K` of `e ≥ t` edges of `𝒢` at `(v, t)`
  carrying a set `Σ` of replacement events with `|Σ| ≥ (e - τ)/a`;
* `forgetting` (`thm:forgetting`, `fgt:eq-main`):
  `P(X_t(v) ≠ Y_t(v)) ≤ 2 ε^{-τ/a} β^t / (1 - β)` under the common-noise coupling;
* `forgetting_tv` (`fgt:eq-tv`): `δ_O(t) ≤ 2 |O| ε^{-τ/a} β^t / (1 - β)`;
* `forgets_of_refutable`: the process forgets.

**[choice]** The paper's hypotheses `j ≥ 1` and `k ≥ 2` are not used by the proof (only
`k ≥ 2j` is, in `fgt:cover`), and `ε < 1` is weakened to `ε ≤ 1`; the Lean statements are
therefore slightly stronger than the printed ones. Likewise `fgt:packing` is proved without its
hypothesis `τ ≥ 1` (at time `0` nothing is marked, so the case `τ = 0` is vacuous), which removes
the separate treatment of `τ = 0` (`L_R = ∅`) in the proof of `thm:forgetting`.
-/
import FixedNoiseErgodicity.Section3.Peierls
import FixedNoiseErgodicity.Section3.Constants
import FixedNoiseErgodicity.Section2.Ergodic
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section

namespace FNE

open MeasureTheory Filter Topology TokenGame
open scoped ENNReal

variable {k : ℕ} {R : WangSet} {j : ℕ}

/-! ## `fgt:path` -/

/-- **`fgt:path`.** Fix `x` and the noise; let `X`, `Y` be the runs from `x` and from `⊥`. If
`X_t(v) ≠ Y_t(v)`, there are sites `p t = v, p (t-1), …, p 0` such that `X_s(p s) ≠ Y_s(p s)` for
`s ≤ t`, and for `s < t` the point `(p (s+1), s+1)` is not an event and `p s ∈ p (s+1) + 𝒩`. -/
theorem discrepancy_path (x : Config k R) (ω : Noise k R) :
    ∀ (t : ℕ) (v : Site k), run x ω t v ≠ run (fun _ => Sym.bot) ω t v →
      ∃ p : ℕ → Site k, p t = v ∧
        (∀ s ≤ t, run x ω s (p s) ≠ run (fun _ => Sym.bot) ω s (p s)) ∧
        ∀ s < t, (ω (s, p (s + 1))).1 = false ∧
          ∃ d ∈ box 1, ∃ i : Option (Fin k), p s = p (s + 1) + (d, provider k i) := by
  intro t
  induction t with
  | zero =>
    intro v hv
    refine ⟨fun _ => v, rfl, fun s hs => ?_, fun s hs => absurd hs (Nat.not_lt_zero s)⟩
    rw [Nat.le_zero.mp hs]
    exact hv
  | succ t ih =>
    intro v hv
    have hflag : (ω (t, v)).1 = false := by
      by_contra h
      rw [Bool.not_eq_false] at h
      apply hv
      rw [run_succ, run_succ, if_pos h, if_pos h]
    rw [run_succ, run_succ, if_neg (by simp [hflag]), if_neg (by simp [hflag])] at hv
    obtain ⟨d, hd, i, hdi⟩ : ∃ d ∈ box 1, ∃ i : Option (Fin k),
        run x ω t (v + (d, provider k i)) ≠
          run (fun _ => Sym.bot) ω t (v + (d, provider k i)) := by
      by_contra h
      push Not at h
      exact hv (quorumRule_local h)
    obtain ⟨p, hpt, hne, hstep⟩ := ih _ hdi
    refine ⟨fun s => if s = t + 1 then v else p s, by simp, fun s hs => ?_, fun s hs => ?_⟩
    · by_cases h : s = t + 1
      · subst h
        simp only [if_true]
        rw [run_succ, run_succ, if_neg (by simp [hflag]), if_neg (by simp [hflag])]
        exact hv
      · simp only [h, if_false]
        exact hne s (by omega)
    · by_cases h : s = t
      · subst h
        simp only [if_true, show s ≠ s + 1 from by omega, if_false]
        exact ⟨hflag, d, hd, i, hpt⟩
      · simp only [show s + 1 ≠ t + 1 from by omega, show s ≠ t + 1 from by omega, if_false]
        exact hstep s (by omega)

/-! ## `fgt:packing` -/

theorem reach_mono {K K' : Finset (Sym2 (STPoint k))} (h : K ⊆ K') {a b : STPoint k}
    (hr : EdgeCount.Reach K a b) : EdgeCount.Reach K' a b :=
  Relation.ReflTransGen.mono (fun _ _ hxy => h hxy) _ _ hr

/-- The slabs of `fgt:packing`. Let `p` be a path of marked non-events at the times `τ … t`.
Then for every `T ∈ [τ, t]` there are a set `K` of edges of `𝒢` and a set `Σ` of events at times
`≤ T`, lying on `K`, every vertex of `K` reachable inside `K` from some path point `(p s, s)`,
`s ≤ T`, and a time `s' ≤ τ` with `T + 1 ≤ s' + q²|Σ|` and `|K| ≤ q²|Σ|`. (Contours at
`ρ_l = (p t_l, t_l)`, `t_{l+1} = s_l - 1`, have disjoint time slabs `[s_l, t_l]`.) -/
theorem slabs {η : ℕ × Site k → Bool} {τ t : ℕ} (p : ℕ → Site k)
    (hp : ∀ s, τ ≤ s → s ≤ t → (p s, s) ∈ markedSet η ∧ (p s, s) ∉ eventSet η) :
    ∀ T, τ ≤ T → T ≤ t → ∃ (K : Finset (Sym2 (STPoint k))) (Sig : Finset (STPoint k)) (s' : ℕ),
      s' ≤ τ ∧ (∀ e ∈ K, IsGEdge e) ∧ (∀ φ ∈ Sig, φ ∈ eventSet η) ∧
      (∀ φ ∈ Sig, φ.2 ≤ T) ∧ (∀ φ ∈ Sig, ∃ e ∈ K, φ ∈ e) ∧
      (∀ e ∈ K, ∀ w ∈ e, ∃ s ≤ T, EdgeCount.Reach K (p s, s) w) ∧
      T + 1 ≤ s' + (k + 1) ^ 2 * Sig.card ∧ K.card ≤ (k + 1) ^ 2 * Sig.card := by
  classical
  intro T
  induction T using Nat.strong_induction_on with
  | _ T ih =>
  intro hτT hTt
  obtain ⟨hmark, hnev⟩ := hp T hτT hTt
  obtain ⟨m, hm2, Sig₁, K₁, hSigU, hcard, hconn, hedge, -, hSigK, -, hKle, s₁, ⟨φ₁, hφ₁, hs₁⟩,
    hmin, htime, hcross⟩ := contourG (markedSet η) (eventSet η) (marked_hasSupports η) hmark hnev
  subst hcard
  simp only at hcross
  set Q := (k + 1) ^ 2 with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have hlink : Q * (Sig₁.card - 1) + Q = Q * Sig₁.card := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  have hG₁ : ∀ e ∈ K₁, IsGEdge e := by
    intro e he
    obtain ⟨θ, θ', i, -, -, hl, -, rfl⟩ := hedge e he
    exact ⟨θ, θ', i, hl, rfl⟩
  have hSigT : ∀ φ ∈ Sig₁, φ.2 ≤ T := by
    intro φ hφ
    obtain ⟨e, he, hφe⟩ := hSigK φ hφ
    exact (htime e he φ hφe).2
  have hs₁T : s₁ ≤ T := hs₁ ▸ hSigT φ₁ hφ₁
  have hreach₁ : ∀ e ∈ K₁, ∀ w ∈ e, ∃ s ≤ T, EdgeCount.Reach K₁ (p s, s) w :=
    fun e he w hw => ⟨T, le_rfl, hconn e he w hw⟩
  by_cases hcase : τ + 1 ≤ s₁
  · obtain ⟨K₂, Sig₂, s', hs'τ, hG₂, hev₂, hT₂, hSigK₂, hreach₂, hcount₂, hKcard₂⟩ :=
      ih (s₁ - 1) (by omega) (by omega) (by omega)
    have hdisj : Disjoint Sig₁ Sig₂ := by
      rw [Finset.disjoint_left]
      intro φ h1 h2
      have := hmin φ h1
      have := hT₂ φ h2
      omega
    refine ⟨K₁ ∪ K₂, Sig₁ ∪ Sig₂, s', hs'τ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_union.mp he with h | h
      · exact hG₁ e h
      · exact hG₂ e h
    · intro φ hφ
      rcases Finset.mem_union.mp hφ with h | h
      · exact hSigU φ h
      · exact hev₂ φ h
    · intro φ hφ
      rcases Finset.mem_union.mp hφ with h | h
      · exact hSigT φ h
      · have := hT₂ φ h
        omega
    · intro φ hφ
      rcases Finset.mem_union.mp hφ with h | h
      · obtain ⟨e, he, hφe⟩ := hSigK φ h
        exact ⟨e, Finset.mem_union_left _ he, hφe⟩
      · obtain ⟨e, he, hφe⟩ := hSigK₂ φ h
        exact ⟨e, Finset.mem_union_right _ he, hφe⟩
    · intro e he w hw
      rcases Finset.mem_union.mp he with h | h
      · obtain ⟨s, hs, hr⟩ := hreach₁ e h w hw
        exact ⟨s, hs, reach_mono Finset.subset_union_left hr⟩
      · obtain ⟨s, hs, hr⟩ := hreach₂ e h w hw
        exact ⟨s, by omega, reach_mono Finset.subset_union_right hr⟩
    · rw [Finset.card_union_of_disjoint hdisj, Nat.mul_add]
      omega
    · have := Finset.card_union_le K₁ K₂
      rw [Finset.card_union_of_disjoint hdisj, Nat.mul_add]
      omega
  · refine ⟨K₁, Sig₁, s₁, by omega, hG₁, hSigU, hSigT, hSigK, hreach₁, by omega, by omega⟩

/-- **`fgt:packing`.** Let `k ≥ 2j` and `S_τ(0, …, 0) = ∅` for the box `V_r`. Fix
`x` and the noise. If `t ≥ τ` and `X_t(v) ≠ Y_t(v)`, there are a set `K` of `e ≥ t` edges of `𝒢`,
connected at `(v, t)`, and a set `Σ` of replacement events, each an end of an edge of `K`, with
`|Σ| ≥ (e - τ)/a`, `a = 2q² + 1`. -/
theorem packing (hk : 2 * j ≤ k) {r τ : ℕ}
    (hτ : ∀ s : Fin j → LiveSymbol R, (origin, s) ∉ tables R j r τ)
    (x : Config k R) (ω : Noise k R) {t : ℕ} (ht : τ ≤ t) {v : Site k}
    (hne : run x ω t v ≠ run (fun _ => Sym.bot) ω t v) :
    ∃ (K : Finset (Sym2 (STPoint k))) (Sig : Finset (STPoint k)),
      t ≤ K.card ∧ (∀ e ∈ K, IsGEdge e) ∧ EdgeCount.ConnectedAt K (v, t) ∧
      (∀ φ ∈ Sig, ∃ e ∈ K, φ ∈ e) ∧ (∀ φ ∈ Sig, φ ∈ eventSet ω.flags) ∧
      ((K.card : ℝ) - τ) / (2 * ((k : ℝ) + 1) ^ 2 + 1) ≤ Sig.card := by
  classical
  obtain ⟨p, hpt, hpne, hstep⟩ := discrepancy_path x ω t v hne
  have hp : ∀ s, τ ≤ s → s ≤ t →
      (p s, s) ∈ markedSet ω.flags ∧ (p s, s) ∉ eventSet ω.flags := by
    intro s hτs hst
    refine ⟨?_, ?_⟩
    · show domField ω.flags s (p s)
      have hn := hpne s hst
      cases hX : run x ω s (p s) with
      | live b => exact live_marked hk hτ x ω hτs (p s) b hX
      | bot =>
        rw [hX] at hn
        cases hY : run (fun _ => Sym.bot) ω s (p s) with
        | live b => exact live_marked hk hτ _ ω hτs (p s) b hY
        | bot => exact absurd hY.symm hn
    · rintro ⟨s', hs', hη⟩
      simp only at hs'
      subst hs'
      have hf := (hstep s' (by omega)).1
      simp only [Noise.flags] at hη
      rw [hf] at hη
      exact Bool.false_ne_true hη
  obtain ⟨K', Sig, s', hs'τ, hG', hev, -, hSigK', hreach', hcount, hKcard'⟩ :=
    slabs p hp t ht le_rfl
  let edge : ℕ → Sym2 (STPoint k) := fun s => s((p (s + 1), s + 1), (p s, s))
  let pathE : Finset (Sym2 (STPoint k)) := (Finset.range t).image edge
  have hinj : Function.Injective edge := by
    intro a b hab
    rcases Sym2.eq_iff.mp hab with ⟨h1, -⟩ | ⟨h1, h2⟩
    · have := congrArg Prod.snd h1
      simp only at this
      omega
    · have e1 := congrArg Prod.snd h1
      have e2 := congrArg Prod.snd h2
      simp only at e1 e2
      omega
  have hpathcard : pathE.card = t := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  set K := pathE ∪ K' with hKdef
  have hedge_mem : ∀ s < t, edge s ∈ K := fun s hs =>
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr hs, rfl⟩)
  have hpathReach : ∀ n s, s + n = t → EdgeCount.Reach K (p t, t) (p s, s) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      rw [Nat.add_zero] at hs
      subst hs
      exact Relation.ReflTransGen.refl
    | succ n ihn =>
      intro s hs
      have h1 := ihn (s + 1) (by omega)
      exact Relation.ReflTransGen.tail h1 (hedge_mem s (by omega))
  have hreachPath : ∀ s ≤ t, EdgeCount.Reach K (p t, t) (p s, s) :=
    fun s hs => hpathReach (t - s) s (by omega)
  refine ⟨K, Sig, ?_, ?_, ?_, ?_, hev, ?_⟩
  · rw [← hpathcard]
    exact Finset.card_le_card Finset.subset_union_left
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨-, d, hd, i, hpi⟩ := hstep s (Finset.mem_range.mp hs)
      exact ⟨(p (s + 1), s + 1), (p s, s), i, ⟨rfl, d, hd, by rw [hpi]; rfl⟩, rfl⟩
    · exact hG' e h
  · intro e he w hw
    rw [← hpt]
    rcases Finset.mem_union.mp he with h | h
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp h
      have hs' := Finset.mem_range.mp hs
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hreachPath (s + 1) (by omega)
      · exact hreachPath s (by omega)
    · obtain ⟨s, hs, hr⟩ := hreach' e h w hw
      exact (hreachPath s (by omega)).trans (reach_mono Finset.subset_union_right hr)
  · intro φ hφ
    obtain ⟨e, he, hφe⟩ := hSigK' φ hφ
    exact ⟨e, Finset.mem_union_right _ he, hφe⟩
  · have hKle : K.card ≤ t + (k + 1) ^ 2 * Sig.card := by
      have : K.card ≤ pathE.card + K'.card := Finset.card_union_le pathE K'
      omega
    have hnat : K.card + 1 ≤ τ + 2 * ((k + 1) ^ 2 * Sig.card) := by omega
    have hreal : (K.card : ℝ) + 1 ≤ τ + 2 * (((k : ℝ) + 1) ^ 2 * Sig.card) := by
      exact_mod_cast hnat
    rw [div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ Sig.card := Nat.cast_nonneg _
    nlinarith

/-! ## `thm:forgetting` -/

/-- **`thm:forgetting`**, the bound `fgt:eq-main`. Let `k ≥ 2j`, let `R` be `j`-token refutable
with time `τ`, `0 < ε ≤ 1` and `β = 2 D₀² ε^{1/a} < 1`. Under the common-noise coupling, for every
configuration `x`, site `v` and time `t`:
`P(X_t(v) ≠ Y_t(v)) ≤ 2 ε^{-τ/a} β^t / (1 - β)`, where `X` runs from `x` and `Y` from `⊥`. -/
theorem forgetting (hk : 2 * j ≤ k) {τ : ℕ} (hR : RefutableWithTime R j τ) {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε ≤ 1) (hβ : beta k ε < 1) (x : Config k R) (v : Site k) (t : ℕ) :
    noiseLaw k R ε {ω | run x ω t v ≠ run (fun _ => Sym.bot) ω t v} ≤
      ENNReal.ofReal (2 * ε ^ (-(τ : ℝ) / (2 * ((k : ℝ) + 1) ^ 2 + 1)) * beta k ε ^ t /
        (1 - beta k ε)) := by
  obtain ⟨r, hr⟩ := hR
  haveI := isProbabilityMeasure_noiseLaw (k := k) (R := R) h0.le h1
  have ha : (0 : ℝ) < 2 * ((k : ℝ) + 1) ^ 2 + 1 := by positivity
  have hβ0 := beta_nonneg k h0.le
  by_cases htτ : t < τ
  · -- before the refutation time the bound exceeds `1`
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hX : 1 ≤ ε ^ (-(τ : ℝ) / (2 * ((k : ℝ) + 1) ^ 2 + 1)) * beta k ε ^ t := by
      unfold beta
      rw [mul_pow, ← Real.rpow_natCast (ε ^ _), ← Real.rpow_mul h0.le, mul_left_comm,
        ← Real.rpow_add h0]
      have hD : (1 : ℝ) ≤ 2 * (50 * ((k : ℝ) + 1)) ^ 2 := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      have hpow : (1 : ℝ) ≤ (2 * (50 * ((k : ℝ) + 1)) ^ 2) ^ t := one_le_pow₀ hD
      have hexp : (1 : ℝ) ≤ ε ^ (-(τ : ℝ) / (2 * ((k : ℝ) + 1) ^ 2 + 1) +
          1 / (2 * ((k : ℝ) + 1) ^ 2 + 1) * (t : ℝ)) := by
        refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 ?_
        have : (t : ℝ) ≤ τ := by exact_mod_cast htτ.le
        rw [show -(τ : ℝ) / (2 * ((k : ℝ) + 1) ^ 2 + 1) + 1 / (2 * ((k : ℝ) + 1) ^ 2 + 1) * t
            = ((t : ℝ) - τ) / (2 * ((k : ℝ) + 1) ^ 2 + 1) from by ring]
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
      calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
        _ ≤ _ := mul_le_mul hpow hexp zero_le_one (by positivity)
    rw [le_div_iff₀ (by linarith)]
    linarith
  · -- after the refutation time: packing and the Peierls sum
    push Not at htτ
    have := peierls (R := R) h0 h1 (-(τ : ℝ) / (2 * ((k : ℝ) + 1) ^ 2 + 1))
      (1 / (2 * ((k : ℝ) + 1) ^ 2 + 1)) hβ ((v, t) : STPoint k) t
      {ω | run x ω t v ≠ run (fun _ => Sym.bot) ω t v} (fun ω hω => ?_)
    · exact this
    obtain ⟨K, Sig, htK, hG, hconn, hSigK, hev, hbound⟩ := packing hk hr x ω htτ hω
    refine ⟨K.card, htK, K, rfl, hG, hconn, Sig, fun φ hφ => Or.inr (hSigK φ hφ), ?_, hev⟩
    calc -(τ : ℝ) / (2 * ((k : ℝ) + 1) ^ 2 + 1) + 1 / (2 * ((k : ℝ) + 1) ^ 2 + 1) * (K.card : ℝ)
        = ((K.card : ℝ) - τ) / (2 * ((k : ℝ) + 1) ^ 2 + 1) := by ring
      _ ≤ (Sig.card : ℝ) := hbound

/-! ## The total-variation form `fgt:eq-tv` -/

/-- `P_x(X_t ∈ A)` as a probability of the noise. -/
theorem law_dirac_apply {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (x : Config k R) (t : ℕ)
    {A : Set (Config k R)} (hA : MeasurableSet A) :
    law k R ε (Measure.dirac x) t A = noiseLaw k R ε {ω | run x ω t ∈ A} := by
  have hm : Measurable (fun ω : Noise k R => run x ω t) :=
    (measurable_run t).comp measurable_prodMk_left
  rw [law_dirac h0 h1, Measure.map_apply hm hA]
  rfl

/-- A coupling bound on a window: `|P(X ∈ cyl) - P(Y ∈ cyl)| ≤ Σ_{v ∈ O} P(X_t(v) ≠ Y_t(v))`. -/
theorem abs_cyl_sub_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (x y : Config k R) (t : ℕ)
    (O : Finset (Site k)) (E : Set (O → Sym R)) {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ v ∈ O, noiseLaw k R ε {ω | run x ω t v ≠ run y ω t v} ≤ ENNReal.ofReal c) :
    |(law k R ε (Measure.dirac x) t (cyl O E)).toReal -
        (law k R ε (Measure.dirac y) t (cyl O E)).toReal| ≤ O.card * c := by
  haveI := isProbabilityMeasure_noiseLaw (k := k) (R := R) h0 h1
  rw [law_dirac_apply h0 h1 x t (measurableSet_cyl O E),
    law_dirac_apply h0 h1 y t (measurableSet_cyl O E)]
  set D : Set (Noise k R) := ⋃ v ∈ O, {ω | run x ω t v ≠ run y ω t v} with hD
  have hDle : noiseLaw k R ε D ≤ ENNReal.ofReal (O.card * c) := by
    calc noiseLaw k R ε D ≤ ∑ v ∈ O, noiseLaw k R ε {ω | run x ω t v ≠ run y ω t v} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ v ∈ O, ENNReal.ofReal c := Finset.sum_le_sum hv
      _ = ENNReal.ofReal (O.card * c) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
  have hsub : ∀ (a b : Config k R), (∀ v ∈ O, a v = b v) → (a ∈ cyl O E ↔ b ∈ cyl O E) := by
    intro a b hab
    have : (fun w : O => a w.1) = fun w : O => b w.1 := funext fun w => hab w.1 w.2
    simp only [cyl, Set.mem_setOf_eq, this]
  have h1' : {ω : Noise k R | run x ω t ∈ cyl O E} ⊆ {ω | run y ω t ∈ cyl O E} ∪ D := by
    intro ω hω
    by_cases hall : ∀ v ∈ O, run x ω t v = run y ω t v
    · exact Or.inl ((hsub _ _ hall).mp hω)
    · push Not at hall
      obtain ⟨v, hv, hne⟩ := hall
      exact Or.inr (Set.mem_biUnion hv hne)
  have h2' : {ω : Noise k R | run y ω t ∈ cyl O E} ⊆ {ω | run x ω t ∈ cyl O E} ∪ D := by
    intro ω hω
    by_cases hall : ∀ v ∈ O, run x ω t v = run y ω t v
    · exact Or.inl ((hsub _ _ hall).mpr hω)
    · push Not at hall
      obtain ⟨v, hv, hne⟩ := hall
      exact Or.inr (Set.mem_biUnion hv hne)
  have hDr : (noiseLaw k R ε D).toReal ≤ O.card * c :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hDle
  rw [← measureReal_def] at hDr
  rw [← measureReal_def, ← measureReal_def, abs_sub_le_iff]
  constructor
  · have := (measureReal_mono (μ := noiseLaw k R ε) h1' (measure_ne_top _ _)).trans (measureReal_union_le _ _)
    linarith
  · have := (measureReal_mono (μ := noiseLaw k R ε) h2' (measure_ne_top _ _)).trans (measureReal_union_le _ _)
    linarith

/-- **`thm:forgetting`**, the bound `fgt:eq-tv`: for every finite window `O` and time `t`,
`δ_O(t) = sup_x dtv(Law_x(X_t|_O), Law_⊥(X_t|_O)) ≤ 2 |O| ε^{-τ/a} β^t / (1 - β)`. -/
theorem forgetting_tv (hk : 2 * j ≤ k) {τ : ℕ} (hR : RefutableWithTime R j τ) {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε ≤ 1) (hβ : beta k ε < 1) (O : Finset (Site k)) (t : ℕ) :
    deltaO k R ε O t ≤ 2 * O.card * ε ^ (-(τ : ℝ) / (2 * ((k : ℝ) + 1) ^ 2 + 1)) *
      beta k ε ^ t / (1 - beta k ε) := by
  have hβ0 := beta_nonneg k h0.le
  have hc : 0 ≤ 2 * ε ^ (-(τ : ℝ) / (2 * ((k : ℝ) + 1) ^ 2 + 1)) * beta k ε ^ t /
      (1 - beta k ε) := div_nonneg (by positivity) (by linarith)
  refine deltaO_le_of (fun x => dtv_le_of (fun E => ?_))
  refine (abs_cyl_sub_le h0.le h1 x _ t O E hc
    (fun v _ => forgetting hk hR h0 h1 hβ x v t)).trans_eq ?_
  ring

/-- **`thm:forgetting`**, last sentence: the noisy rule forgets its initial configuration. -/
theorem forgets_of_refutable (hk : 2 * j ≤ k) {τ : ℕ} (hR : RefutableWithTime R j τ) {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε ≤ 1) (hβ : beta k ε < 1) : Forgets k R ε := by
  intro O
  have hβ0 := beta_nonneg k h0.le
  set C := 2 * O.card * ε ^ (-(τ : ℝ) / (2 * ((k : ℝ) + 1) ^ 2 + 1)) / (1 - beta k ε)
  have hlim : Tendsto (fun t : ℕ => C * beta k ε ^ t) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ).const_mul C
  refine squeeze_zero (fun t => deltaO_nonneg ε O t) (fun t => ?_) hlim
  refine (forgetting_tv hk hR h0 h1 hβ O t).trans_eq ?_
  simp only [C]
  ring

end FNE

end
