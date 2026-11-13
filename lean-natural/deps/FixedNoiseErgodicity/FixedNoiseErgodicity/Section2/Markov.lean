/-
# Section 2.2: the one-step product form and the Markov property

* the noise splits into its first time slice and the (shifted) rest, independent, with laws
  `sliceLaw` and `noiseLaw` (`noiseLaw_map_splitN`);
* `law (δ_x) 1 = ⊗_v ((1 - ε) δ_{F(x)(v)} + ε · uniform)` (`law_dirac_one`; clause (iii) of
  `IsPositiveRatePCA`);
* the Markov property `μΦ^{t+1} = (μΦ^t)Φ` (`law_succ`) and `μΦ^{t+1} = (μΦ)Φ^t` (`law_succ'`).
-/
import FixedNoiseErgodicity.Section2.Process

set_option autoImplicit false

noncomputable section

namespace FNE

open MeasureTheory
open scoped ENNReal

variable {k : ℕ} {R : WangSet}

/-! ## The first time slice and the rest of the noise -/

/-- The first time slice of the noise: `v ↦ (η_1(v), ζ_1(v))`. -/
def slice0 (ω : Noise k R) : Site k → Bool × Sym R := fun v => ω (0, v)

/-- The noise after the first step, shifted back by one unit of time. -/
def shiftN (ω : Noise k R) : Noise k R := fun p => ω (p.1 + 1, p.2)

/-- The split of the noise into its first slice and the rest. -/
def splitN (ω : Noise k R) : (Site k → Bool × Sym R) × Noise k R := (slice0 ω, shiftN ω)

/-- One step of the process from `x` driven by the noise slice `ζ`. -/
def step (x : Config k R) (ζ : Site k → Bool × Sym R) : Config k R :=
  fun v => if (ζ v).1 then (ζ v).2 else quorumRule k R x v

theorem run_one (x : Config k R) (ω : Noise k R) : run x ω 1 = step x (slice0 ω) := rfl

theorem run_succ_shift (x : Config k R) (ω : Noise k R) (t : ℕ) :
    run x ω (t + 1) = run (run x ω 1) (shiftN ω) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext v
    rw [run_succ, run_succ, ← ih]
    rfl

theorem measurable_slice0 : Measurable (slice0 (k := k) (R := R)) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

theorem measurable_shiftN : Measurable (shiftN (k := k) (R := R)) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

theorem measurable_splitN : Measurable (splitN (k := k) (R := R)) :=
  measurable_slice0.prodMk measurable_shiftN

theorem measurable_step :
    Measurable (fun q : Config k R × (Site k → Bool × Sym R) => step q.1 q.2) := by
  refine Measurable.of_eval (fun v => ?_)
  have hflag : Measurable (fun q : Config k R × (Site k → Bool × Sym R) => (q.2 v).1) :=
    measurable_fst.comp ((measurable_pi_apply v).comp measurable_snd)
  have hval : Measurable (fun q : Config k R × (Site k → Bool × Sym R) => (q.2 v).2) :=
    measurable_snd.comp ((measurable_pi_apply v).comp measurable_snd)
  exact Measurable.ite (hflag (measurableSet_singleton true)) hval
    ((measurable_quorumRule_apply v).comp measurable_fst)

/-- The law of one time slice of the noise. -/
abbrev sliceLaw (k : ℕ) (R : WangSet) (ε : ℝ) : Measure (Site k → Bool × Sym R) :=
  Measure.infinitePi (fun _ : Site k => noiseSite R ε)

/-- Reindexing `Site ⊕ (ℕ × Site) → ℕ × Site`: `inl v ↦ (0, v)`, `inr (t, v) ↦ (t + 1, v)`. -/
def splitIdx : Site k ⊕ (ℕ × Site k) → ℕ × Site k
  | .inl v => (0, v)
  | .inr p => (p.1 + 1, p.2)

theorem splitIdx_injective : Function.Injective (splitIdx (k := k)) := by
  rintro (v | ⟨t, v⟩) (v' | ⟨t', v'⟩) h <;> simp_all [splitIdx]

/-- The first time slice and the rest of the noise are independent, with laws `sliceLaw` and
`noiseLaw`. -/
theorem noiseLaw_map_splitN {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (noiseLaw k R ε).map splitN = (sliceLaw k R ε).prod (noiseLaw k R ε) := by
  haveI := isProbabilityMeasure_noiseSite (R := R) h0 h1
  haveI := isProbabilityMeasure_noiseLaw (k := k) (R := R) h0 h1
  let E := MeasurableEquiv.sumPiEquivProdPi (fun _ : Site k ⊕ (ℕ × Site k) => Bool × Sym R)
  have hsum : ((sliceLaw k R ε).prod (noiseLaw k R ε)).map E.symm =
      Measure.infinitePi (fun _ : Site k ⊕ (ℕ × Site k) => noiseSite R ε) := by
    refine Measure.eq_infinitePi _ (fun s t ht => ?_)
    rw [Measure.map_apply E.symm.measurable
      (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
    have hpre : E.symm ⁻¹' (Set.pi (s : Set (Site k ⊕ (ℕ × Site k))) t) =
        (Set.pi (s.toLeft : Set (Site k)) (fun v => t (.inl v))) ×ˢ
          (Set.pi (s.toRight : Set (ℕ × Site k)) (fun p => t (.inr p))) := by
      ext ⟨f, g⟩
      simp [E, MeasurableEquiv.coe_sumPiEquivProdPi_symm, Set.mem_pi, Sum.forall]
    rw [hpre, Measure.prod_prod, sliceLaw, noiseLaw,
      Measure.infinitePi_pi _ (fun i _ => ht (.inl i)),
      Measure.infinitePi_pi _ (fun i _ => ht (.inr i))]
    conv_rhs => rw [← Finset.toLeft_disjSum_toRight (u := s)]
    rw [Finset.prod_disjSum]
  have hre : Measurable (fun (ω : Noise k R) (i : Site k ⊕ (ℕ × Site k)) => ω (splitIdx i)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  have h2 : (noiseLaw k R ε).map (fun ω i => ω (splitIdx i)) =
      Measure.infinitePi (fun _ : Site k ⊕ (ℕ × Site k) => noiseSite R ε) :=
    Measure.map_infinitePi_infinitePi_of_inj splitIdx_injective
  have hcomp : (splitN : Noise k R → _) = E ∘ (fun ω i => ω (splitIdx i)) := by
    funext ω
    rfl
  rw [hcomp, ← Measure.map_map E.measurable hre, h2, ← hsum,
    Measure.map_map E.measurable E.symm.measurable, MeasurableEquiv.self_comp_symm,
    Measure.map_id]

theorem noiseLaw_map_slice0 {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (noiseLaw k R ε).map slice0 = sliceLaw k R ε := by
  haveI := isProbabilityMeasure_noiseLaw (k := k) (R := R) h0 h1
  have : (noiseLaw k R ε).map slice0 = ((noiseLaw k R ε).map splitN).map Prod.fst := by
    rw [Measure.map_map measurable_fst measurable_splitN]
    rfl
  rw [this, noiseLaw_map_splitN h0 h1, Measure.map_fst_prod, measure_univ, one_smul]

/-! ## The one-step product form -/

/-- The image of the one-site noise law under `(b, s) ↦ (b ? s : a)` is
`(1 - ε) δ_a + ε · uniform`. -/
theorem noiseSite_map_eq {ε : ℝ} (a : Sym R) :
    (noiseSite R ε).map (fun b : Bool × Sym R => if b.1 then b.2 else a) =
      ENNReal.ofReal (1 - ε) • Measure.dirac a + ENNReal.ofReal ε • uniformSym R := by
  have hg : Measurable (fun b : Bool × Sym R => if b.1 then b.2 else a) :=
    measurable_of_countable _
  rw [noiseSite, flagLaw, Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.dirac_prod, Measure.dirac_prod, Measure.map_add _ _ hg, (Measure.map_smul _ hg.aemeasurable),
    (Measure.map_smul _ hg.aemeasurable), Measure.map_map hg measurable_prodMk_left,
    Measure.map_map hg measurable_prodMk_left]
  have e1 : ((fun b : Bool × Sym R => if b.1 then b.2 else a) ∘ Prod.mk true) = id := by
    funext s
    rfl
  have e2 : ((fun b : Bool × Sym R => if b.1 then b.2 else a) ∘ Prod.mk false) =
      fun _ => a := by
    funext s
    rfl
  rw [e1, e2, Measure.map_id, Measure.map_const, measure_univ, one_smul, add_comm]

/-- **`set:def-noise`, the displayed formula; clause (iii) of `IsPositiveRatePCA`.** Given
`X_0 = x`, the values `X_1(v)` are independent with laws `(1 - ε) δ_{F(x)(v)} + ε · uniform`. -/
theorem law_dirac_one {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (x : Config k R) :
    law k R ε (Measure.dirac x) 1 = Measure.infinitePi (fun v => siteLaw k R ε x v) := by
  haveI := isProbabilityMeasure_noiseSite (R := R) h0 h1
  have hg : ∀ v : Site k,
      Measurable (fun b : Bool × Sym R => if b.1 then b.2 else quorumRule k R x v) :=
    fun _ => measurable_of_countable _
  have key := Measure.infinitePi_map_pi (fun _ : Site k => noiseSite R ε)
    (f := fun v (b : Bool × Sym R) => if b.1 then b.2 else quorumRule k R x v) hg
  have hgm : Measurable (fun (ζ : Site k → Bool × Sym R) v =>
      if (ζ v).1 then (ζ v).2 else quorumRule k R x v) :=
    Measurable.of_eval (fun v => (hg v).comp (measurable_pi_apply v))
  rw [law_dirac h0 h1]
  have e : (fun ω : Noise k R => run x ω 1) = (fun (ζ : Site k → Bool × Sym R) v =>
      if (ζ v).1 then (ζ v).2 else quorumRule k R x v) ∘ slice0 := by
    funext ω
    rfl
  rw [e, ← Measure.map_map hgm measurable_slice0, noiseLaw_map_slice0 h0 h1]
  refine key.trans ?_
  congr 1
  funext v
  exact noiseSite_map_eq _

/-! ## The Markov property -/

/-- `μΦ^{t+1} = (μΦ)Φ^t`: the process after one step is the process from `X_1`. -/
theorem law_succ' {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure (Config k R))
    [IsProbabilityMeasure μ] (t : ℕ) :
    law k R ε μ (t + 1) = law k R ε (law k R ε μ 1) t := by
  haveI := isProbabilityMeasure_noiseLaw (k := k) (R := R) h0 h1
  haveI := isProbabilityMeasure_noiseSite (R := R) h0 h1
  have hrun := measurable_run (k := k) (R := R) t
  have hstep := measurable_step (k := k) (R := R)
  let H : (Config k R × (Site k → Bool × Sym R)) × Noise k R → Config k R :=
    fun q => run (step q.1.1 q.1.2) q.2 t
  have hH : Measurable H := hrun.comp ((hstep.comp measurable_fst).prodMk measurable_snd)
  let G : Config k R × ((Site k → Bool × Sym R) × Noise k R) → Config k R :=
    fun z => run (step z.1 z.2.1) z.2.2 t
  have hG : Measurable G :=
    hrun.comp ((hstep.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd))
  -- the left side
  have hL : law k R ε μ (t + 1) =
      ((μ.prod (sliceLaw k R ε)).prod (noiseLaw k R ε)).map H := by
    have e1 : (fun p : Config k R × Noise k R => run p.1 p.2 (t + 1)) =
        G ∘ Prod.map id splitN := by
      funext p
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, G]
      rw [run_succ_shift, run_one]
      rfl
    have hPM := Measure.map_prod_map μ (noiseLaw k R ε) measurable_id
      (measurable_splitN (k := k) (R := R))
    rw [Measure.map_id, noiseLaw_map_splitN h0 h1] at hPM
    unfold law
    rw [e1, ← Measure.map_map hG (measurable_id.prodMap measurable_splitN), ← hPM,
      ← Measure.prodAssoc_prod, Measure.map_map hG MeasurableEquiv.prodAssoc.measurable]
    rfl
  -- the right side
  have hS : law k R ε μ 1 = (μ.prod (sliceLaw k R ε)).map (fun q => step q.1 q.2) := by
    have hPM := Measure.map_prod_map μ (noiseLaw k R ε) measurable_id
      (measurable_slice0 (k := k) (R := R))
    rw [Measure.map_id, noiseLaw_map_slice0 h0 h1] at hPM
    unfold law
    rw [hPM, Measure.map_map hstep (measurable_id.prodMap measurable_slice0)]
    rfl
  have hPM2 := Measure.map_prod_map (μ.prod (sliceLaw k R ε)) (noiseLaw k R ε) hstep
    measurable_id
  rw [Measure.map_id] at hPM2
  rw [hL, hS]
  unfold law
  rw [hPM2, Measure.map_map hrun (hstep.prodMap measurable_id)]
  rfl

/-- **The Markov property** (`set:def-noise`): `μΦ^{t+1} = (μΦ^t)Φ`. -/
theorem law_succ {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∀ (t : ℕ) (μ : Measure (Config k R)) [IsProbabilityMeasure μ],
      law k R ε μ (t + 1) = law k R ε (law k R ε μ t) 1 := by
  intro t
  induction t with
  | zero =>
    intro μ _
    rw [law_zero h0 h1]
  | succ t ih =>
    intro μ _
    haveI := isProbabilityMeasure_law h0 h1 μ 1
    haveI := isProbabilityMeasure_law h0 h1 μ (t + 1)
    rw [law_succ' h0 h1 μ (t + 1), ih (law k R ε μ 1), ← law_succ' h0 h1 μ t]

/-- **Clause (iv) of `IsPositiveRatePCA`** (positive rates, `set:def-noise`): for `ε > 0`, every
symbol has probability at least `ε / |𝒜_R| > 0` under every `siteLaw x v`. -/
theorem siteLaw_pos {ε : ℝ} (hε : 0 < ε) (x : Config k R) (v : Site k) (s : Sym R) :
    0 < siteLaw k R ε x v {s} := by
  have h1 : 0 < ENNReal.ofReal ε * uniformSym R {s} := by
    rw [uniformSym_singleton]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hε).ne' (ENNReal.inv_ne_zero.mpr (by simp))
  refine lt_of_lt_of_le h1 ?_
  simp only [siteLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  exact le_add_self

end FNE

end
