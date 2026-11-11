/-
# Section 8 (second half): `M ↦ R_M` is computable

**`computable_familyR : Computable familyR`.** By `familyR_eq` (`Family/Decide.lean`), `familyR M`
is the concatenation, over the explicit (constant) list of routed tiles, of a `filterMap` over the
explicit list `quads M` of quadruples of sublists of `𝒰_M`, with the palettes checked on lists.
Every step is primitive recursive, by Mathlib's `Primrec` combinators:
* the constructors and case analyses of `OSym`, `OState`, `CASym`, `Fact` (through the equivalences
  of `Family/Codes.lean`), and the projections of `TuringMachine`;
* the machine `M°` (`oHalt`, `oTr`, from the table of `M` by `List.lookup`) and the local rule
  `next` of its cellular automaton;
* the bound `bnd M` and the lists `osymList`, `ostateList`, `sList`, `hList`, `uList`, `quads`
  (`List.sublists` is a fold);
* the checks `PalChk`: membership, equality of the sets of entries of two lists, and the clauses
  `SatAtL` at the nine sites of `Λ`; and the tile code (`colCodeL`, a fold).

No axiom or hypothesis is added: `Computable` is Mathlib's notion, and every lemma below is proved.
-/
import FixedNoiseErgodicity.Family.Decide

set_option autoImplicit false

noncomputable section

namespace FNE.Family

open FNE

/-! ## Generic helpers -/

section Helpers

variable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

theorem primrecPred_const (c : Prop) [Decidable c] : PrimrecPred fun _ : α => c :=
  Primrec.primrecPred (Primrec.const (decide c))

theorem primrecPred_imp {p q : α → Prop} (hp : PrimrecPred p) (hq : PrimrecPred q) :
    PrimrecPred fun a => p a → q a :=
  (hp.not.or hq).of_eq fun a => by tauto

/-- Membership in a list is primitive recursive. -/
theorem primrec_mem [DecidableEq α] : PrimrecRel fun (b : α) (L : List α) => b ∈ L :=
  ((PrimrecRel.exists_mem_list (Primrec.eq (α := α))).swap).of_eq fun b L => by
    simp [Function.swap]

omit [Primcodable β] in
/-- A `flatMap` over a fixed list, of functions that are primitive recursive. -/
theorem primrec_flatMap_const {f : α → β → List σ} (L : List β)
    (hf : ∀ b ∈ L, Primrec fun a => f a b) : Primrec fun a => L.flatMap (f a) := by
  induction L with
  | nil => exact Primrec.const []
  | cons b L ih =>
    simp only [List.flatMap_cons]
    exact Primrec.list_append.comp (hf b (by simp)) (ih fun b' hb' => hf b' (by simp [hb']))

omit [Primcodable β] in
/-- A conjunction over a fixed list, of predicates that are primitive recursive. -/
theorem primrecPred_forall_const {p : α → β → Prop} (L : List β)
    (hp : ∀ b ∈ L, PrimrecPred fun a => p a b) : PrimrecPred fun a => ∀ b ∈ L, p a b := by
  induction L with
  | nil => exact (primrecPred_const True).of_eq fun a => by simp
  | cons b L ih =>
    exact ((hp b (by simp)).and (ih fun b' hb' => hp b' (by simp [hb']))).of_eq fun a => by simp

/-- `m ^ n` is primitive recursive. -/
theorem primrec_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- `List.sublists` (a fold) is primitive recursive. -/
theorem primrec_sublists : Primrec (@List.sublists β) := by
  have h : Primrec fun p : List β × β × List (List β) => p.2.2.flatMap fun x => [x, p.2.1 :: x] :=
    Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp Primrec.snd
        (Primrec.list_cons.comp
          (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
          (Primrec.const []))).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const [[]]) h.to₂).of_eq fun l => rfl

end Helpers

/-! ## Machines, symbols, states, facts -/

theorem primrec_table : Primrec TuringMachine.table :=
  Primrec.fst.comp (Primrec.of_equiv (e := TuringMachine.equivProd))

theorem primrec_halting : Primrec TuringMachine.halting :=
  Primrec.snd.comp (Primrec.of_equiv (e := TuringMachine.equivProd))

theorem primrec_osym_equiv : Primrec OSym.equiv := Primrec.of_equiv

theorem primrec_osym_mk : Primrec fun p : Bool × ℕ × ℕ => (⟨p.1, p.2.1, p.2.2⟩ : OSym) :=
  Primrec.of_equiv_symm (e := OSym.equiv)

theorem primrec_mark : Primrec OSym.mark := Primrec.fst.comp primrec_osym_equiv

theorem primrec_up : Primrec OSym.up := Primrec.fst.comp (Primrec.snd.comp primrec_osym_equiv)

theorem primrec_lo : Primrec OSym.lo := Primrec.snd.comp (Primrec.snd.comp primrec_osym_equiv)

theorem primrec_get : Primrec fun p : OSym × Bool => p.1.get p.2 :=
  (Primrec.cond Primrec.snd (primrec_lo.comp Primrec.fst) (primrec_up.comp Primrec.fst)).of_eq
    fun ⟨γ, l⟩ => by cases l <;> rfl

theorem primrec_set : Primrec fun p : OSym × Bool × ℕ => p.1.set p.2.1 p.2.2 :=
  (Primrec.cond (Primrec.fst.comp Primrec.snd)
    (primrec_osym_mk.comp (Primrec.pair (primrec_mark.comp Primrec.fst)
      (Primrec.pair (primrec_up.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))))
    (primrec_osym_mk.comp (Primrec.pair (primrec_mark.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.snd) (primrec_lo.comp Primrec.fst))))).of_eq
    fun ⟨γ, l, a⟩ => by cases l <;> rfl

theorem primrec_ostate_equiv : Primrec OState.equiv := Primrec.of_equiv

theorem primrec_ostate_symm : Primrec OState.equiv.symm := Primrec.of_equiv_symm

theorem primrec_sim : Primrec fun p : ℕ × Bool => OState.sim p.1 p.2 :=
  (primrec_ostate_symm.comp
    (Primrec.option_some.comp (Primrec.pair (Primrec.const false) Primrec.id))).of_eq
    fun ⟨_, _⟩ => rfl

theorem primrec_back : Primrec fun p : ℕ × Bool => OState.back p.1 p.2 :=
  (primrec_ostate_symm.comp
    (Primrec.option_some.comp (Primrec.pair (Primrec.const true) Primrec.id))).of_eq
    fun ⟨_, _⟩ => rfl

theorem primrec_casym_equiv : Primrec (CASym.equiv OState OSym) := Primrec.of_equiv

theorem primrec_casym_symm : Primrec (CASym.equiv OState OSym).symm := Primrec.of_equiv_symm

theorem primrec_tape : Primrec (CASym.tape : OSym → MSym) :=
  (primrec_casym_symm.comp
    (Primrec.option_some.comp (Primrec.pair (Primrec.const none) Primrec.id))).of_eq
    fun _ => rfl

theorem primrec_head : Primrec fun p : OState × OSym => (CASym.head p.1 p.2 : MSym) :=
  (primrec_casym_symm.comp (Primrec.option_some.comp
    (Primrec.pair (Primrec.option_some.comp Primrec.fst) Primrec.snd))).of_eq fun ⟨_, _⟩ => rfl

theorem primrec_fact_equiv : Primrec Fact.equiv := Primrec.of_equiv

theorem primrec_fact_symm : Primrec Fact.equiv.symm := Primrec.of_equiv_symm

theorem primrec_P : Primrec Fact.P :=
  (primrec_fact_symm.comp (Primrec.option_some.comp
    (Primrec.option_some.comp Primrec.option_some))).of_eq fun _ => rfl

theorem primrec_sym? : Primrec Fact.sym? :=
  (Primrec.option_bind primrec_fact_equiv
    ((Primrec.option_bind₁ (Primrec.id (α := Option MSym))).comp Primrec.snd).to₂).of_eq
    fun F => by cases F <;> rfl

theorem primrec_syms : Primrec syms :=
  Primrec.listFilterMap Primrec.id (primrec_sym?.comp Primrec.snd).to₂

/-! ## The machine `M°` and the rule `next` -/

theorem oHalt_eq (M : TuringMachine) (q : OState) :
    oHalt M q = Option.casesOn (OState.equiv q) false
      fun p => !p.1 && decide (p.2.1 ∈ M.halting) := by
  cases q <;> rfl

theorem primrec_oHalt : Primrec fun p : TuringMachine × OState => oHalt p.1 p.2 := by
  have hm : Primrec fun p : TuringMachine × ℕ => decide (p.2 ∈ p.1.halting) :=
    primrec_mem.decide.comp Primrec.snd (primrec_halting.comp Primrec.fst)
  have hg : Primrec fun x : (TuringMachine × OState) × (Bool × ℕ × Bool) =>
      !x.2.1 && decide (x.2.2.1 ∈ x.1.1.halting) :=
    Primrec.and.comp (Primrec.not.comp (Primrec.fst.comp Primrec.snd))
      (hm.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  exact (Primrec.option_casesOn (primrec_ostate_equiv.comp Primrec.snd) (Primrec.const false)
    hg.to₂).of_eq fun p => (oHalt_eq p.1 p.2).symm

theorem primrec_haltHead : Primrec fun p : TuringMachine × MSym => haltHead p.1 p.2 := by
  have hq : Primrec fun z : ((TuringMachine × MSym) × (Option OState × OSym)) × OState =>
      oHalt z.1.1.1 z.2 :=
    primrec_oHalt.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
  have hv : Primrec fun w : (TuringMachine × MSym) × (Option OState × OSym) =>
      (Option.casesOn w.2.1 false fun q => oHalt w.1.1 q : Bool) :=
    Primrec.option_casesOn (Primrec.fst.comp Primrec.snd) (Primrec.const false) hq.to₂
  refine (Primrec.option_casesOn (primrec_casym_equiv.comp Primrec.snd) (Primrec.const false)
    hv.to₂).of_eq fun ⟨M, b⟩ => ?_
  cases b <;> rfl

instance : Finite Move := Finite.of_equiv _ Move.equivFin.symm

theorem primrec_oMove : Primrec fun p : Bool × Bool × Move => oMove p.1 p.2.1 p.2.2 :=
  Primrec.dom_finite _

/-- `List.lookup` in the table of a machine (with the `BEq` instance of pairs). -/
theorem primrec_lookup :
    Primrec fun p : (ℕ × ℕ) × List ((ℕ × ℕ) × (ℕ × ℕ × Move)) => p.2.lookup p.1 :=
  Primrec.listLookup.of_eq fun k l => by rw [lawful_beq_subsingleton instBEqOfDecidableEq]

/-- The `sim` case of `oTr`. -/
def simCase (M : TuringMachine) (n : ℕ) (l : Bool) (γ : OSym) : OState × OSym × Bool :=
  Option.casesOn (M.table.lookup (n, γ.get l)) (OState.back n l, γ, true) fun v =>
    Option.casesOn (oMove l γ.mark v.2.2).2
      (OState.back v.1 (oMove l γ.mark v.2.2).1, γ.set l v.2.1, true)
      fun r => (OState.sim v.1 (oMove l γ.mark v.2.2).1, γ.set l v.2.1, r)

theorem oTr_eq (M : TuringMachine) (q : OState) (γ : OSym) :
    oTr M q γ = Option.casesOn (OState.equiv q)
      ((OState.back 0 false, (⟨true, γ.up, γ.lo⟩ : OSym), true) : OState × OSym × Bool)
      fun p => bif p.1 then (OState.sim p.2.1 p.2.2, γ, false) else simCase M p.2.1 p.2.2 γ := by
  cases q with
  | init => rfl
  | back n l => rfl
  | sim n l =>
    show _ = simCase M n l γ
    simp only [oTr, simCase]
    rcases M.table.lookup (n, γ.get l) with _ | ⟨q', a', m⟩
    · rfl
    · dsimp only
      rcases oMove l γ.mark m with ⟨l', _ | r⟩ <;> rfl

theorem primrec_simCase :
    Primrec fun x : TuringMachine × ℕ × Bool × OSym => simCase x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  have hn : Primrec fun x : TuringMachine × ℕ × Bool × OSym => x.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hl : Primrec fun x : TuringMachine × ℕ × Bool × OSym => x.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hγ : Primrec fun x : TuringMachine × ℕ × Bool × OSym => x.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hlk : Primrec fun x : TuringMachine × ℕ × Bool × OSym =>
      x.1.table.lookup (x.2.1, x.2.2.2.get x.2.2.1) :=
    primrec_lookup.comp (Primrec.pair (Primrec.pair hn (primrec_get.comp (Primrec.pair hγ hl)))
      (primrec_table.comp Primrec.fst))
  have h0 : Primrec fun x : TuringMachine × ℕ × Bool × OSym =>
      ((OState.back x.2.1 x.2.2.1, x.2.2.2, true) : OState × OSym × Bool) :=
    Primrec.pair (primrec_back.comp (Primrec.pair hn hl)) (Primrec.pair hγ (Primrec.const true))
  have hmv : Primrec fun y : (TuringMachine × ℕ × Bool × OSym) × (ℕ × ℕ × Move) =>
      oMove y.1.2.2.1 y.1.2.2.2.mark y.2.2.2 :=
    primrec_oMove.comp (Primrec.pair (hl.comp Primrec.fst) (Primrec.pair
      (primrec_mark.comp (hγ.comp Primrec.fst)) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hset : Primrec fun y : (TuringMachine × ℕ × Bool × OSym) × (ℕ × ℕ × Move) =>
      y.1.2.2.2.set y.1.2.2.1 y.2.2.1 :=
    primrec_set.comp (Primrec.pair (hγ.comp Primrec.fst) (Primrec.pair (hl.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  have hq : Primrec fun y : (TuringMachine × ℕ × Bool × OSym) × (ℕ × ℕ × Move) => y.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hs : Primrec fun y : (TuringMachine × ℕ × Bool × OSym) × (ℕ × ℕ × Move) =>
      (Option.casesOn (oMove y.1.2.2.1 y.1.2.2.2.mark y.2.2.2).2
        (OState.back y.2.1 (oMove y.1.2.2.1 y.1.2.2.2.mark y.2.2.2).1,
          y.1.2.2.2.set y.1.2.2.1 y.2.2.1, true)
        fun r => (OState.sim y.2.1 (oMove y.1.2.2.1 y.1.2.2.2.mark y.2.2.2).1,
          y.1.2.2.2.set y.1.2.2.1 y.2.2.1, r) : OState × OSym × Bool) :=
    Primrec.option_casesOn (Primrec.snd.comp hmv)
      (Primrec.pair (primrec_back.comp (Primrec.pair hq (Primrec.fst.comp hmv)))
        (Primrec.pair hset (Primrec.const true)))
      (Primrec.pair (primrec_sim.comp (Primrec.pair (hq.comp Primrec.fst)
        (Primrec.fst.comp (hmv.comp Primrec.fst)))) (Primrec.pair (hset.comp Primrec.fst)
          Primrec.snd)).to₂
  exact (Primrec.option_casesOn hlk h0 hs.to₂).of_eq fun _ => rfl

theorem primrec_oTr : Primrec fun x : TuringMachine × OState × OSym => oTr x.1 x.2.1 x.2.2 := by
  have hγ : Primrec fun x : TuringMachine × OState × OSym => x.2.2 :=
    Primrec.snd.comp Primrec.snd
  have h0 : Primrec fun x : TuringMachine × OState × OSym =>
      ((OState.back 0 false, (⟨true, x.2.2.up, x.2.2.lo⟩ : OSym), true) : OState × OSym × Bool) :=
    Primrec.pair (Primrec.const _) (Primrec.pair (primrec_osym_mk.comp (Primrec.pair
      (Primrec.const true) (Primrec.pair (primrec_up.comp hγ) (primrec_lo.comp hγ))))
      (Primrec.const true))
  have hs : Primrec fun y : (TuringMachine × OState × OSym) × (Bool × ℕ × Bool) =>
      bif y.2.1 then ((OState.sim y.2.2.1 y.2.2.2, y.1.2.2, false) : OState × OSym × Bool)
      else simCase y.1.1 y.2.2.1 y.2.2.2 y.1.2.2 :=
    Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (primrec_sim.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.pair (hγ.comp Primrec.fst) (Primrec.const false)))
      (primrec_simCase.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (hγ.comp Primrec.fst)))))
  exact (Primrec.option_casesOn (primrec_ostate_equiv.comp (Primrec.fst.comp Primrec.snd)) h0
    hs.to₂).of_eq fun x => (oTr_eq x.1 x.2.1 x.2.2).symm

theorem fromLeft_eq (M : TuringMachine) (a : MSym) :
    fromLeft (oTr M) (oHalt M) a = Option.bind (CASym.equiv OState OSym a) fun v =>
      Option.bind v.1 fun q =>
        bif !oHalt M q && (oTr M q v.2).2.2 then some (oTr M q v.2).1 else none := by
  cases a with
  | head q γ => exact (cond_eq_ite _ _ _).symm
  | _ => rfl

theorem fromRight_eq (M : TuringMachine) (a : MSym) :
    fromRight (oTr M) (oHalt M) a = Option.bind (CASym.equiv OState OSym a) fun v =>
      Option.bind v.1 fun q =>
        bif !oHalt M q && !(oTr M q v.2).2.2 then some (oTr M q v.2).1 else none := by
  cases a with
  | head q γ => exact (cond_eq_ite _ _ _).symm
  | _ => rfl

/-- The pieces `oTr M q γ` and `oHalt M q` in a context `((x, (·, γ)), q)`. -/
theorem primrec_ctx_tr {α : Type*} [Primcodable α] {m : α → TuringMachine} (hm : Primrec m) :
    Primrec fun z : (α × (Option OState × OSym)) × OState => oTr (m z.1.1) z.2 z.1.2.2 :=
  primrec_oTr.comp (Primrec.pair (hm.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))

theorem primrec_ctx_halt {α : Type*} [Primcodable α] {m : α → TuringMachine} (hm : Primrec m) :
    Primrec fun z : (α × (Option OState × OSym)) × OState => oHalt (m z.1.1) z.2 :=
  primrec_oHalt.comp (Primrec.pair (hm.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)

theorem primrec_fromLeft :
    Primrec fun x : TuringMachine × MSym => fromLeft (oTr x.1) (oHalt x.1) x.2 := by
  have htr := primrec_ctx_tr (α := TuringMachine × MSym) Primrec.fst
  have hh := primrec_ctx_halt (α := TuringMachine × MSym) Primrec.fst
  have hin := Primrec.cond (Primrec.and.comp (Primrec.not.comp hh)
    (Primrec.snd.comp (Primrec.snd.comp htr))) (Primrec.option_some.comp (Primrec.fst.comp htr))
    (Primrec.const none)
  have hmid := Primrec.option_bind (Primrec.fst.comp Primrec.snd) hin.to₂
  exact (Primrec.option_bind (primrec_casym_equiv.comp Primrec.snd) hmid.to₂).of_eq
    fun x => (fromLeft_eq x.1 x.2).symm

theorem primrec_fromRight :
    Primrec fun x : TuringMachine × MSym => fromRight (oTr x.1) (oHalt x.1) x.2 := by
  have htr := primrec_ctx_tr (α := TuringMachine × MSym) Primrec.fst
  have hh := primrec_ctx_halt (α := TuringMachine × MSym) Primrec.fst
  have hin := Primrec.cond (Primrec.and.comp (Primrec.not.comp hh)
    (Primrec.not.comp (Primrec.snd.comp (Primrec.snd.comp htr))))
    (Primrec.option_some.comp (Primrec.fst.comp htr)) (Primrec.const none)
  have hmid := Primrec.option_bind (Primrec.fst.comp Primrec.snd) hin.to₂
  exact (Primrec.option_bind (primrec_casym_equiv.comp Primrec.snd) hmid.to₂).of_eq
    fun x => (fromRight_eq x.1 x.2).symm

theorem next_eq (M : TuringMachine) (a b c : MSym) :
    next (oTr M) (oHalt M) a b c =
      Option.casesOn (CASym.equiv OState OSym b) CASym.wall fun v =>
        Option.casesOn v.1
          (Option.casesOn (fromLeft (oTr M) (oHalt M) a <|> fromRight (oTr M) (oHalt M) c)
            (CASym.tape v.2) fun q => CASym.head q v.2)
          fun q => bif oHalt M q then CASym.head q v.2 else CASym.tape (oTr M q v.2).2.1 := by
  cases b with
  | wall => rfl
  | tape γ =>
    show _ = (Option.casesOn (fromLeft (oTr M) (oHalt M) a <|> fromRight (oTr M) (oHalt M) c)
      (CASym.tape γ) fun q => CASym.head q γ : MSym)
    simp only [next]
    rcases fromLeft (oTr M) (oHalt M) a with _ | q <;>
      rcases fromRight (oTr M) (oHalt M) c with _ | q' <;> rfl
  | head q γ =>
    show _ = bif oHalt M q then CASym.head q γ else CASym.tape (oTr M q γ).2.1
    simp only [next]
    cases oHalt M q <;> rfl

theorem primrec_next : Primrec fun x : TuringMachine × MSym × MSym × MSym =>
    next (oTr x.1) (oHalt x.1) x.2.1 x.2.2.1 x.2.2.2 := by
  have hor : Primrec fun x : TuringMachine × MSym × MSym × MSym =>
      (fromLeft (oTr x.1) (oHalt x.1) x.2.1 <|> fromRight (oTr x.1) (oHalt x.1) x.2.2.2) :=
    Primrec.option_orElse.comp
      (primrec_fromLeft.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)))
      (primrec_fromRight.comp (Primrec.pair Primrec.fst
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have htape : Primrec fun w : (TuringMachine × MSym × MSym × MSym) × (Option OState × OSym) =>
      (Option.casesOn (fromLeft (oTr w.1.1) (oHalt w.1.1) w.1.2.1 <|>
        fromRight (oTr w.1.1) (oHalt w.1.1) w.1.2.2.2) (CASym.tape w.2.2)
          fun q => CASym.head q w.2.2 : MSym) := Primrec.option_casesOn (hor.comp Primrec.fst)
    (primrec_tape.comp (Primrec.snd.comp Primrec.snd))
    (primrec_head.comp (Primrec.pair Primrec.snd
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).to₂
  have hhead : Primrec fun z : ((TuringMachine × MSym × MSym × MSym) × (Option OState × OSym)) ×
      OState => (bif oHalt z.1.1.1 z.2 then CASym.head z.2 z.1.2.2
        else CASym.tape (oTr z.1.1.1 z.2 z.1.2.2).2.1 : MSym) := Primrec.cond
    (primrec_ctx_halt (α := TuringMachine × MSym × MSym × MSym) Primrec.fst)
    (primrec_head.comp (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
    (primrec_tape.comp (Primrec.fst.comp (Primrec.snd.comp
      (primrec_ctx_tr (α := TuringMachine × MSym × MSym × MSym) Primrec.fst))))
  have hv : Primrec fun w : (TuringMachine × MSym × MSym × MSym) × (Option OState × OSym) =>
      (Option.casesOn w.2.1 (Option.casesOn (fromLeft (oTr w.1.1) (oHalt w.1.1) w.1.2.1 <|>
        fromRight (oTr w.1.1) (oHalt w.1.1) w.1.2.2.2) (CASym.tape w.2.2)
          fun q => CASym.head q w.2.2) fun q => bif oHalt w.1.1 q then CASym.head q w.2.2
            else CASym.tape (oTr w.1.1 q w.2.2).2.1 : MSym) :=
    Primrec.option_casesOn (Primrec.fst.comp Primrec.snd) htape hhead.to₂
  exact (Primrec.option_casesOn (primrec_casym_equiv.comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))) (Primrec.const CASym.wall) hv.to₂).of_eq
    fun x => (next_eq x.1 x.2.1 x.2.2.1 x.2.2.2).symm

/-! ## The explicit lists -/

theorem primrec_bnd : Primrec bnd := by
  have hmax : Primrec fun e : (ℕ × ℕ) × (ℕ × ℕ × Move) => max e.2.1 e.2.2.1 :=
    Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hl : Primrec fun M : TuringMachine => M.table.map fun e => max e.2.1 e.2.2.1 :=
    Primrec.list_map primrec_table (hmax.comp Primrec.snd).to₂
  exact (Primrec.succ.comp (Primrec.list_foldr hl (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)).of_eq fun _ => rfl

theorem primrec_osymList : Primrec osymList := by
  have hin : Primrec fun p : ℕ × ℕ =>
      (List.range p.1).flatMap fun v => [(⟨false, p.2, v⟩ : OSym), ⟨true, p.2, v⟩] :=
    Primrec.list_flatMap (Primrec.list_range.comp Primrec.fst)
      (Primrec.list_cons.comp (primrec_osym_mk.comp (Primrec.pair (Primrec.const false)
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)))
        (Primrec.list_cons.comp (primrec_osym_mk.comp (Primrec.pair (Primrec.const true)
          (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))) (Primrec.const []))).to₂
  exact (Primrec.list_flatMap Primrec.list_range hin.to₂).of_eq fun B => rfl

theorem primrec_ostateList : Primrec ostateList := by
  have h4 : Primrec fun p : ℕ × ℕ =>
      [OState.sim p.2 false, OState.sim p.2 true, OState.back p.2 false, OState.back p.2 true] :=
    Primrec.list_cons.comp (primrec_sim.comp (Primrec.pair Primrec.snd (Primrec.const false)))
      (Primrec.list_cons.comp (primrec_sim.comp (Primrec.pair Primrec.snd (Primrec.const true)))
        (Primrec.list_cons.comp (primrec_back.comp (Primrec.pair Primrec.snd (Primrec.const false)))
          (Primrec.list_cons.comp (primrec_back.comp (Primrec.pair Primrec.snd
            (Primrec.const true))) (Primrec.const []))))
  exact (Primrec.list_cons.comp (Primrec.const OState.init)
    (Primrec.list_flatMap Primrec.list_range h4.to₂)).of_eq fun B => rfl

theorem primrec_sList : Primrec sList := by
  have h1 : Primrec fun B => (osymList B).map (CASym.tape : OSym → MSym) :=
    Primrec.list_map primrec_osymList (primrec_tape.comp Primrec.snd).to₂
  have h2 : Primrec fun B => (ostateList B).flatMap fun q =>
      (osymList B).map (CASym.head q : OSym → MSym) :=
    Primrec.list_flatMap primrec_ostateList (Primrec.list_map (primrec_osymList.comp Primrec.fst)
      (primrec_head.comp (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂).to₂
  exact (Primrec.list_cons.comp (Primrec.const CASym.wall) (Primrec.list_append.comp h1 h2)).of_eq
    fun B => rfl

theorem primrec_hList : Primrec hList :=
  (Primrec.list_cons.comp (Primrec.const Fact.seed) (Primrec.list_cons.comp
    (Primrec.const Fact.start) (Primrec.list_cons.comp (Primrec.const Fact.ray)
      (Primrec.list_map (primrec_sList.comp primrec_bnd) (primrec_P.comp Primrec.snd).to₂)))).of_eq
    fun _ => rfl

theorem primrec_uList : Primrec uList := by
  have h : ∀ (b : Bool) (y : Plane), Primrec fun M : TuringMachine =>
      (hList M).map fun F => ((b, y, F) : Atom) := fun b y =>
    Primrec.list_map primrec_hList
      (Primrec.pair (Primrec.const b) (Primrec.pair (Primrec.const y) Primrec.snd)).to₂
  have h2 : ∀ b : Bool, Primrec fun M : TuringMachine =>
      lamList.flatMap fun y => (hList M).map fun F => ((b, y, F) : Atom) := fun b =>
    primrec_flatMap_const (f := fun M y => (hList M).map fun F => ((b, y, F) : Atom)) lamList
      fun y _ => h b y
  exact (primrec_flatMap_const
    (f := fun M b => lamList.flatMap fun y => (hList M).map fun F => ((b, y, F) : Atom))
    [false, true] fun b _ => h2 b).of_eq fun M => rfl

theorem primrec_quads : Primrec quads := by
  have hs : Primrec fun M : TuringMachine => (uList M).sublists :=
    primrec_sublists.comp primrec_uList
  have h4 : Primrec fun x : ((TuringMachine × List Atom) × List Atom) × List Atom =>
      (uList x.1.1.1).sublists.map fun n => ((x.1.1.2, x.1.2, x.2, n) : Quad) :=
    Primrec.list_map (hs.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂
  have h3 : Primrec fun x : (TuringMachine × List Atom) × List Atom =>
      (uList x.1.1).sublists.flatMap fun s =>
        (uList x.1.1).sublists.map fun n => ((x.1.2, x.2, s, n) : Quad) :=
    Primrec.list_flatMap (hs.comp (Primrec.fst.comp Primrec.fst)) h4.to₂
  have h2 : Primrec fun x : TuringMachine × List Atom =>
      (uList x.1).sublists.flatMap fun e => (uList x.1).sublists.flatMap fun s =>
        (uList x.1).sublists.map fun n => ((x.2, e, s, n) : Quad) :=
    Primrec.list_flatMap (hs.comp Primrec.fst) h3.to₂
  exact (Primrec.list_flatMap hs h2.to₂).of_eq fun M => rfl

/-! ## The tile code -/

theorem primrec_addBit : Primrec fun p : ℕ × ℕ => addBit p.1 p.2 :=
  (Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.snd
    (primrec_pow.comp (Primrec.const 2) Primrec.fst)) (Primrec.const 2)) (Primrec.const 1))
    Primrec.snd (Primrec.nat_add.comp Primrec.snd
      (primrec_pow.comp (Primrec.const 2) Primrec.fst))).of_eq fun _ => rfl

theorem primrec_atomCode : Primrec atomCode := Primrec.encode

theorem primrec_colCodeL : Primrec colCodeL :=
  (Primrec.list_foldr Primrec.id (Primrec.const 0) (primrec_addBit.comp (Primrec.pair
    (primrec_atomCode.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun _ => rfl

theorem primrec_tileCode (r : RTile) : Primrec (tileCode r) := by
  have hT : Primrec fun p : ℕ × ℕ × ℕ × ℕ => Tile.equivProd.symm p := Primrec.of_equiv_symm
  exact (hT.comp (Primrec.pair
    (Primrec₂.natPair.comp (Primrec.const (Encodable.encode (r.q.colN, r.fN)))
      (primrec_colCodeL.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (Primrec.pair (Primrec₂.natPair.comp (Primrec.const (Encodable.encode (r.q.colE, r.fE)))
      (primrec_colCodeL.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.pair (Primrec₂.natPair.comp (Primrec.const (Encodable.encode (r.q.colS, r.fS)))
        (primrec_colCodeL.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
        (Primrec₂.natPair.comp (Primrec.const (Encodable.encode (r.q.colW, r.fW)))
          (primrec_colCodeL.comp Primrec.fst)))))).of_eq fun _ => rfl

/-! ## The checks -/

theorem primrec_setEq : PrimrecRel SetEq := by
  have h1 : PrimrecRel fun l l' : List Atom => ∀ x ∈ l, x ∈ l' :=
    PrimrecRel.forall_mem_list primrec_mem
  exact (PrimrecPred.and h1 h1.swap).of_eq fun p => Iff.rfl

theorem primrec_selAt (y : Plane) : Primrec (selAt y) :=
  (Primrec.ite ((Primrec.eq.comp Primrec.fst (Primrec.const false)).and
    (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const y)))
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)).of_eq
    fun _ => rfl

theorem primrec_recSite (y : Plane) : Primrec fun q : Quad => recSite q y := by
  by_cases h : 0 ≤ y.1
  · exact (Primrec.listFilterMap (Primrec.fst.comp Primrec.snd)
      ((primrec_selAt y).comp Primrec.snd).to₂).of_eq fun q => by simp only [recSite, h, if_true]
  · exact (Primrec.listFilterMap Primrec.fst
      ((primrec_selAt (y + (1, 0))).comp Primrec.snd).to₂).of_eq
      fun q => by simp only [recSite, h, if_false]

theorem primrec_ls (b : Bool) (p : Plane → Prop) [DecidablePred p] (d : Plane) :
    Primrec fun q : Quad => (lamList.filter fun y => p y).flatMap fun y =>
      (recSite q y).map fun F => ((b, y + d, F) : Atom) :=
  primrec_flatMap_const (f := fun q y => (recSite q y).map fun F => ((b, y + d, F) : Atom)) _
    fun y _ => Primrec.list_map (primrec_recSite y)
      (Primrec.pair (Primrec.const b) (Primrec.pair (Primrec.const (y + d)) Primrec.snd)).to₂

theorem primrec_lsW : Primrec fun q : Quad => lsW (recSite q) :=
  (primrec_ls false (fun y => y.1 ≤ 0) (1, 0)).of_eq fun _ => rfl

theorem primrec_lsE : Primrec fun q : Quad => lsE (recSite q) :=
  (primrec_ls false (fun y => 0 ≤ y.1) 0).of_eq fun _ => by simp [lsE]

theorem primrec_lsS : Primrec fun q : Quad => lsS (recSite q) :=
  (primrec_ls true (fun y => y.2 ≤ 0) (0, 1)).of_eq fun _ => rfl

theorem primrec_lsN : Primrec fun q : Quad => lsN (recSite q) :=
  (primrec_ls true (fun y => 0 ≤ y.2) 0).of_eq fun _ => by simp [lsN]

theorem primrecPred_satAtL (ξ : Plane) :
    PrimrecPred fun x : TuringMachine × Quad => SatAtL x.1 (recSite x.2) ξ := by
  have hG : ∀ y, Primrec fun x : TuringMachine × Quad => recSite x.2 y := fun y =>
    (primrec_recSite y).comp Primrec.snd
  have hm : ∀ (F : Fact) (y : Plane),
      PrimrecPred fun x : TuringMachine × Quad => F ∈ recSite x.2 y := fun F y =>
    primrec_mem.comp (Primrec.const F) (hG y)
  have hc : ∀ (c : Prop) [Decidable c], PrimrecPred fun _ : TuringMachine × Quad => c :=
    fun c _ => primrecPred_const c
  -- (H8): three nested quantifiers over the symbols present
  have hR3 : PrimrecRel fun (c : MSym) (w : ((TuringMachine × Quad) × MSym) × MSym) =>
      Fact.P (next (oTr w.1.1.1) (oHalt w.1.1.1) w.1.2 w.2 c) ∈ recSite w.1.1.2 (ξ + (0, 1)) :=
    primrec_mem.comp (primrec_P.comp (primrec_next.comp (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst)))))
      ((primrec_recSite (ξ + (0, 1))).comp
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))
  have hP3 : PrimrecPred fun w : ((TuringMachine × Quad) × MSym) × MSym =>
      ∀ c ∈ syms (recSite w.1.1.2 (ξ + (1, 0))),
        Fact.P (next (oTr w.1.1.1) (oHalt w.1.1.1) w.1.2 w.2 c) ∈ recSite w.1.1.2 (ξ + (0, 1)) :=
    (PrimrecRel.forall_mem_list hR3).comp (primrec_syms.comp ((primrec_recSite (ξ + (1, 0))).comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))) Primrec.id
  have hR2 : PrimrecRel fun (b : MSym) (v : (TuringMachine × Quad) × MSym) =>
      ∀ c ∈ syms (recSite v.1.2 (ξ + (1, 0))),
        Fact.P (next (oTr v.1.1) (oHalt v.1.1) v.2 b c) ∈ recSite v.1.2 (ξ + (0, 1)) :=
    hP3.comp (Primrec.pair Primrec.snd Primrec.fst)
  have hP2 : PrimrecPred fun v : (TuringMachine × Quad) × MSym =>
      ∀ b ∈ syms (recSite v.1.2 ξ), ∀ c ∈ syms (recSite v.1.2 (ξ + (1, 0))),
        Fact.P (next (oTr v.1.1) (oHalt v.1.1) v.2 b c) ∈ recSite v.1.2 (ξ + (0, 1)) :=
    (PrimrecRel.forall_mem_list hR2).comp
      (primrec_syms.comp ((primrec_recSite ξ).comp (Primrec.snd.comp Primrec.fst))) Primrec.id
  have hR1 : PrimrecRel fun (a : MSym) (x : TuringMachine × Quad) =>
      ∀ b ∈ syms (recSite x.2 ξ), ∀ c ∈ syms (recSite x.2 (ξ + (1, 0))),
        Fact.P (next (oTr x.1) (oHalt x.1) a b c) ∈ recSite x.2 (ξ + (0, 1)) :=
    hP2.comp (Primrec.pair Primrec.snd Primrec.fst)
  have h8 : PrimrecPred fun x : TuringMachine × Quad =>
      ∀ a ∈ syms (recSite x.2 (ξ - (1, 0))), ∀ b ∈ syms (recSite x.2 ξ),
        ∀ c ∈ syms (recSite x.2 (ξ + (1, 0))),
          Fact.P (next (oTr x.1) (oHalt x.1) a b c) ∈ recSite x.2 (ξ + (0, 1)) :=
    (PrimrecRel.forall_mem_list hR1).comp
      (primrec_syms.comp ((primrec_recSite (ξ - (1, 0))).comp Primrec.snd)) Primrec.id
  -- (H9)
  have hR9 : PrimrecRel fun (b : MSym) (x : TuringMachine × Quad) => haltHead x.1 b = false :=
    Primrec.eq.comp (primrec_haltHead.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd) Primrec.fst)) (Primrec.const false)
  have h9 : PrimrecPred fun x : TuringMachine × Quad =>
      ∀ b ∈ syms (recSite x.2 ξ), haltHead x.1 b = false :=
    (PrimrecRel.forall_mem_list hR9).comp (primrec_syms.comp (hG ξ)) Primrec.id
  unfold SatAtL
  exact (primrecPred_imp (hm .seed ξ) (hm (.P .wall) ξ)).and
    ((primrecPred_imp (hc _) (primrecPred_imp (hm .seed ξ) (hm .start (ξ + (1, 0))))).and
    ((primrecPred_imp (hm .start ξ) (hm (.P (.head .init OSym.blank)) ξ)).and
    ((primrecPred_imp (hc _) (primrecPred_imp (hm .start ξ) (hm .ray (ξ + (1, 0))))).and
    ((primrecPred_imp (hm .ray ξ) (hm (.P (.tape OSym.blank)) ξ)).and
    ((primrecPred_imp (hc _) (primrecPred_imp (hm .ray ξ) (hm .ray (ξ + (1, 0))))).and
    ((primrecPred_imp (hc _) (primrecPred_imp (hm (.P .wall) ξ) (hm (.P .wall) (ξ + (0, 1))))).and
    ((primrecPred_imp (hc _) (primrecPred_imp (hc _) (primrecPred_imp (hc _) h8))).and h9)))))))

theorem primrecPred_actChk : PrimrecPred fun x : TuringMachine × Quad => ActChk x.1 x.2 := by
  have hs : PrimrecPred fun x : TuringMachine × Quad => ∀ ξ ∈ lamList, SatAtL x.1 (recSite x.2) ξ :=
    primrecPred_forall_const (p := fun (x : TuringMachine × Quad) ξ => SatAtL x.1 (recSite x.2) ξ)
      lamList
      fun ξ _ => primrecPred_satAtL ξ
  have he : ∀ {f g : Quad → List Atom}, Primrec f → Primrec g →
      PrimrecPred fun x : TuringMachine × Quad => SetEq (f x.2) (g x.2) := fun hf hg =>
    primrec_setEq.comp (hf.comp Primrec.snd) (hg.comp Primrec.snd)
  unfold ActChk
  exact hs.and ((he primrec_lsW Primrec.fst).and
    ((he primrec_lsE (Primrec.fst.comp Primrec.snd)).and
    ((he primrec_lsS (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).and
      (he primrec_lsN (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))

theorem primrecPred_palChk (ρ : Role) :
    PrimrecPred fun x : TuringMachine × Quad => PalChk x.1 ρ x.2 := by
  have he : ∀ {f g : Quad → List Atom}, Primrec f → Primrec g →
      PrimrecPred fun x : TuringMachine × Quad => SetEq (f x.2) (g x.2) := fun hf hg =>
    primrec_setEq.comp (hf.comp Primrec.snd) (hg.comp Primrec.snd)
  cases ρ with
  | inactive => exact primrecPred_const True
  | horiz => exact he Primrec.fst (Primrec.fst.comp Primrec.snd)
  | vert =>
    exact he (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  | active => exact primrecPred_actChk
  | seed =>
    exact (he Primrec.fst (Primrec.const _)).and ((he (Primrec.fst.comp Primrec.snd)
      (Primrec.const _)).and ((he (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.const _)).and (he (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.const _))))

/-! ## `M ↦ R_M` is computable -/

theorem primrec_famC : Primrec famC := by
  classical
  refine (primrec_flatMap_const (f := fun (M : TuringMachine) (r : RTile) => if r.InR then
      (quads M).filterMap fun q => if PalChk M r.role q then some (tileCode r q) else none
    else []) rtileList fun r _ => ?_).of_eq fun M => rfl
  by_cases hr : r.InR
  · simp only [hr, if_true]
    exact Primrec.listFilterMap primrec_quads (Primrec.ite (primrecPred_palChk r.role)
      (Primrec.option_some.comp ((primrec_tileCode r).comp Primrec.snd)) (Primrec.const none)).to₂
  · simp only [hr, if_false]
    exact Primrec.const []

/-- `M ↦ R_M` is primitive recursive. -/
theorem primrec_familyR : Primrec familyR :=
  primrec_famC.of_eq fun M => (familyR_eq M).symm

/-- **Section 8: `M ↦ R_M` is computable** (the computability clause of `cor:eight`). -/
theorem computable_familyR : Computable familyR :=
  primrec_familyR.to_comp

end FNE.Family
