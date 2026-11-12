/-
Copyright (c) 2026 Seth Douglas, Nidhal Mghirbi. All rights reserved.
Released under the Apache License 2.0.
Formalization of: S. Douglas and N. Mghirbi, "Forgetting under noise is undecidable", version
2.0.0 (draft of 12 Nov 2026): Theorem D and Theorem A of the introduction (environments `mainD`,
`mainA`), with Section 2 (`sec:natural`, Theorem `nw:classification`) and Section 3
(Corollary `nw:machine`).

# Statement file — FROZEN (session 3, 12 Nov 2026)

Frozen after a blind fidelity read against the paper (`STATEMENT-READ.md`). The read found one
mismatch, which is fixed here: Theorem A is stated as printed, with no hypothesis (`FNR.TheoremA`).
Its note on translation invariance is applied in the docstring of `FNR.NaturalClassification`.
Its sha256 is recorded in `STATUS.md` as the statement of record; this file does not change again.

This file defines, transparently and with no proofs of substance, every object that occurs in the
two printed statements, and states them as the propositions `FNR.NaturalClassification`
(Theorem D) and `FNR.TheoremA` (Theorem A on `ℤ⁶`). As in the three earlier cores, the statement
file holds the propositions; the theorems live in the proof files: `FNR.natural_classification`
in `Main.lean`, and `FNR.theorem_A` in `Reduction.lean`. Every definition carries a docstring
citing the paper passage it mirrors. Fidelity choices are marked **[choice]** and are collected in
`STATUS.md` ("Statement fidelity").

Reused statement-level definitions (exact matches, imported, not copied):
* from the forgetting core (`FixedNoiseErgodicity/Statements.lean`): `FNE.Tile` (a Wang tile with
  natural-number edge colours `N, E, S, W`, with its `Primcodable` instance), `FNE.WangSet`
  (a finite set of tiles), `FNE.Plane` (`ℤ²`), the Turing machines `FNE.TuringMachine` (with their
  `Primcodable` instance) and halting from the blank tape `FNE.TuringMachine.Halts` (the machine
  model of the forgetting core's `FNE.CorEight`), and, through the next item, `FNE.flagLaw` and
  `FNE.WeakTendsto`;
* from the noise-diagram core (`UncomputableNoiseDiagram/Statements.lean`): `UND.Site`, the
  cellular automata `UND.CA` on `ℤ^d` (alphabet `Fin n`, finite neighbourhood, local rule, global
  map `UND.CA.apply`), uniform whole-symbol replacement `UND.CA.uniformLaw`, `UND.CA.noiseLaw`,
  the process `UND.CA.run`, its law `UND.CA.law`, stationarity `UND.CA.IsStationary`, ergodicity
  `UND.CA.IsErgodic` (a unique stationary probability law, and weak convergence to it from every
  initial probability law), the translates `UND.CA.shift`, translation invariance
  `UND.CA.IsTranslationInvariant` (invariance under every translation of `ℤ^d`) and
  `UND.CA.HasTwoTIStationaryLaws` (two distinct translation-invariant stationary probability laws).

Printed statement (Theorem D, introduction; Theorem `nw:classification`). Put `K = 16⁴`, `q = 5K`,
`h = 4K` and `ε_* = (2(18q)²)^(-200)`. For every finite Wang set `R`, a cardinal checker followed
by an `h`-of-`q` quorum in five fixed transverse boxes defines a rule `G_R` on `ℤ⁶` with alphabet
`R ⊔ {⊥}`. At every `0 < ε ≤ ε_*`, uniform whole-symbol replacement after `G_R` is ergodic if and
only if `R` does not tile the plane. If `R` tiles, there are two distinct translation-invariant
stationary laws.

Printed statement (Theorem A, introduction; Corollary `nw:machine`). There is a total computable
map `M ↦ W_M` from Turing machines to finite Wang sets such that, for every `ε ∈ (0, ε_*]`, the
positive-rate automaton obtained from `G_{W_M}` is ergodic if and only if `M` halts.
The printed statement has no hypothesis, and neither has `FNR.TheoremA`.

Also stated:
* `FNR.DominoReduction`: the classical domino reduction of Berger (1966) and Robinson (1971), the
  first sentence of `nw:machine` (paper: "The only undecidability input in this route is the
  classical domino reduction of Berger and Robinson");
* `FNR.TheoremAFromDomino`: Theorem A from that reduction (`DominoReduction → ErgodicityReduction`),
  the route of the paper's proof; a conditional form, weaker than `FNR.TheoremA`, not a printed
  statement;
* `FNR.MachineCorollary`: Corollary `nw:machine` in full (the reduction, the ergodicity clause for
  the same map, and "In particular ergodicity is undecidable at each one of these fixed rates");
* the undecidability form of session 1, `FNR.TheoremAUndecidable` (a corollary, not a printed
  environment; with Berger's theorem "the domino problem is undecidable", `FNR.DominoUndecidable`,
  as its hypothesis), the last sentence of `nw:machine` for the raw inputs `R`.

Not stated here (outside the core, by QB's ruling): the coalescence bound (`nw:coalescence`) of
Theorem `nw:classification`, nilpotency, and the other consequences of Section 3 of the paper.
-/
import UncomputableNoiseDiagram.Statements

set_option autoImplicit false

noncomputable section

namespace FNR

open FNE (Tile WangSet Plane TuringMachine)

/-! ## Tilings (Section 2.2, "Tiles, configurations and noise") -/

/-- Section 2.2: "A finite Wang set `R` tiles the plane if there is `θ : ℤ² → R` whose shared
horizontal and vertical edge colours match. Translations are allowed, rotations and reflections
are not." The tile `θ (u + (1, 0))` sits east of `θ u`, the tile `θ (u + (0, 1))` north of it.
**[choice]** `θ` is a map to tiles with values in `R`. -/
def TilesPlane (R : WangSet) : Prop :=
  ∃ θ : Plane → Tile, (∀ u, θ u ∈ R) ∧
    (∀ u, (θ u).E = (θ (u + (1, 0))).W) ∧ (∀ u, (θ u).N = (θ (u + (0, 1))).S)

/-! ## Sites of `ℤ⁶` (Section 2.2) -/

/-- Section 2.2: "We write a spatial site as `v = (u, P)`, where `u ∈ ℤ²` is planar and
`P ∈ ℤ⁴` is transverse." The site `(u, P)` of `ℤ⁶ = Fin 6 → ℤ` is
`(u.1, u.2, P 0, P 1, P 2, P 3)`.
**[choice]** The planar coordinates are the first two. -/
def site (u : Plane) (P : Fin 4 → ℤ) : UND.Site 6 :=
  Fin.cons (α := fun _ => ℤ) u.1 (Fin.cons (α := fun _ => ℤ) u.2 P)

/-! ## The five provider boxes (Section 2.3, display `nw:boxes`) -/

/-- (`nw:boxes`): the cluster corners `C_0 = 0` and `C_i = 160 e_i` (`1 ≤ i ≤ 4`).
**[choice]** The index set `{0, …, 4}` is `Option (Fin 4)`: `none` is `0`, `some i` is `i + 1`. -/
def corner : Option (Fin 4) → (Fin 4 → ℤ)
  | none => 0
  | some i => fun j => if j = i then 160 else 0

/-- (`nw:boxes`): a provider offset `a ∈ S = S_0 ∪ … ∪ S_4`, `S_i = C_i + {0, …, 15}⁴`, given by
its cluster and its position in the box. There are `q = 5·16⁴` of them; the boxes are disjoint, so
this indexing is a bijection onto `S`. -/
abbrev Provider := Option (Fin 4) × (Fin 4 → Fin 16)

/-- The offset `a = C_i + o ∈ ℤ⁴` of a provider. -/
def offset (π : Provider) : Fin 4 → ℤ := corner π.1 + fun j => ((π.2 j : ℕ) : ℤ)

/-! ## The alphabet and the cardinal checker (Section 2.2) -/

/-- Section 2.2: the alphabet `A_R = R ⊔ {⊥}`; `none` is the blank `⊥`, and `some r` is the live
letter `r ∈ R`. -/
abbrev Letter (R : WangSet) := Option R

/-- Section 2.2: "The cardinal checker `C_R` applied in a planar layer retains the central tile
precisely when all five letters at `u + Γ` are live and the four shared edges at `u` match",
`Γ = {0, ±e₁, ±e₂}`. `Keeps x v c`: the letter at `v` is the tile `c`, and the letters at the
east, west, north and south planar neighbours of `v` (same transverse coordinate) are live tiles
whose shared edges match those of `c`. -/
def Keeps {R : WangSet} (x : UND.Site 6 → Letter R) (v : UND.Site 6) (c : R) : Prop :=
  x v = some c ∧
    (∃ b : R, x (v + site (1, 0) 0) = some b ∧ c.1.E = b.1.W) ∧
    (∃ b : R, x (v + site (-1, 0) 0) = some b ∧ b.1.E = c.1.W) ∧
    (∃ b : R, x (v + site (0, 1) 0) = some b ∧ c.1.N = b.1.S) ∧
    (∃ b : R, x (v + site (0, -1) 0) = some b ∧ b.1.N = c.1.S)

open Classical in
/-- Section 2.2: the checked letter `y(v) = C_R(x(·, P))(u)` at `v = (u, P)`: the central letter
if the check passes, "otherwise it outputs `⊥`". -/
def check {R : WangSet} (x : UND.Site 6 → Letter R) (v : UND.Site 6) : Letter R :=
  if ∃ c, Keeps x v c then x v else none

/-- (`nw:rule`): the number `|{a ∈ S : y(u, P + a) = s}|` of providers whose checked reading at
`v = (u, P)` is the live letter `s`. -/
def votes {R : WangSet} (x : UND.Site 6 → Letter R) (v : UND.Site 6) (s : R) : ℕ :=
  (Finset.univ.filter fun π : Provider => check x (v + site 0 (offset π)) = some s).card

/-- (`nw:boxes`): the quorum `h = 4K = 4·16⁴`. -/
def quorum : ℕ := 4 * 16 ^ 4

open Classical in
/-- (`nw:rule`), the clustered quorum: `G_R(x)(u, P) = s` if `s ∈ R` and at least `h` of the `q`
checked readings `y(u, P + a)`, `a ∈ S`, equal `s`; `⊥` if no such live `s` exists.
**[choice]** The live letter is picked with `Classical.choose`; it is unique because
`2h = 8K > 5K = q` (paper, after (`nw:rule`)), so the choice is immaterial. -/
def natMap (R : WangSet) (x : UND.Site 6 → Letter R) : UND.Site 6 → Letter R := fun v =>
  if h : ∃ s : R, quorum ≤ votes x v s then some h.choose else none

/-! ## The automaton `G_R` on `ℤ⁶` -/

/-- Section 2.2: `Γ = {0, e₁, -e₁, e₂, -e₂}` (planar). -/
def cardinal : Finset Plane := {(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)}

/-- Section 2.3, after (`nw:rule`): "The actual neighbourhood is `Γ × S`." -/
def natNbhd : Finset (UND.Site 6) :=
  (cardinal ×ˢ (Finset.univ : Finset Provider)).image fun p => site p.1 (offset p.2)

/-- The identification of `A_R = R ⊔ {⊥}` with the symbol set `Fin |A_R|` of a `UND.CA`.
**[choice]** Any bijection would do (uniform replacement and ergodicity are invariant under
relabelling the alphabet); `Fintype.equivFin` is used, as for the noise-diagram core's rule. -/
def letterEquiv (R : WangSet) : Letter R ≃ Fin (Fintype.card (Letter R)) :=
  Fintype.equivFin (Letter R)

/-- **The rule `G_R`** (Section 2.3, (`nw:rule`)) as a cellular automaton on `ℤ⁶` with alphabet
`A_R = R ⊔ {⊥}` (through `letterEquiv`) and neighbourhood `Γ × S`: the local rule evaluates
`natMap R` at the origin on the pattern read on the neighbourhood.
**[choice]** Outside the neighbourhood the pattern is extended by `⊥`; `natMap R x 0` reads `x`
only on `Γ × S`, so the extension is immaterial (proved in `Rule/Bridge.lean`). -/
def natCA (R : WangSet) : UND.CA 6 where
  numSymbols := Fintype.card (Letter R)
  numSymbols_pos := Fintype.card_pos
  nbhd := natNbhd
  localRule pat := letterEquiv R (natMap R (fun z =>
    if h : z ∈ natNbhd then (letterEquiv R).symm (pat ⟨z, h⟩) else none) 0)

/-! ## The rate (`nw:constants`) -/

/-- (`nw:constants`): `ε_* = B^{-200}`, `B = 2Δ²`, `Δ = 18q`, `q = 5·16⁴`. -/
def epsStar : ℝ := (((2 * (18 * (5 * 16 ^ 4)) ^ 2 : ℕ) : ℝ) ^ 200)⁻¹

/-! ## Theorem D -/

/-- **Theorem D** (introduction; Theorem `nw:classification` without its coalescence bound): for
every finite Wang set `R` and every `0 < ε ≤ ε_*`, the rule `G_R` with uniform whole-symbol
replacement at rate `ε` is ergodic if and only if `R` does not tile `ℤ²`; and if `R` tiles, there
are two distinct translation-invariant stationary laws.
"Translation-invariant" is the noise-diagram core's `UND.CA.IsTranslationInvariant`: invariance
under every translation of `ℤ⁶`. This is exactly the paper's convention (Section 2.2, "Tiles,
configurations and noise": "Spatial translation invariance always means invariance under every
translation of `ℤ⁶`, unless a smaller group is explicitly named"), so the "spatially
translation-invariant" laws of Theorem `nw:classification` are invariant under all of `ℤ⁶`. The
two laws are probability measures (`UND.CA.HasTwoTIStationaryLaws`). -/
def NaturalClassification : Prop :=
  ∀ (R : WangSet) (ε : ℝ), 0 < ε → ε ≤ epsStar →
    ((natCA R).IsErgodic ε ↔ ¬ TilesPlane R) ∧
      (TilesPlane R → (natCA R).HasTwoTIStationaryLaws ε)

/-! ## Positive-rate automata (Theorem A: "the positive-rate automaton obtained from `G_{W_M}`") -/

/-- Section 2.2 (the noise): the law of `X_1(w)` given `X_0 = x`,
`(1 - ε) δ_{F(x)(w)} + ε · uniform`, for a cellular automaton `F` with uniform whole-symbol
replacement at rate `ε`. (The forgetting core's `FNE.siteLaw`, for an arbitrary automaton.) -/
def siteLaw {d : ℕ} (A : UND.CA d) (ε : ℝ) (x : A.Config) (w : UND.Site d) :
    MeasureTheory.Measure A.Sym :=
  ENNReal.ofReal (1 - ε) • MeasureTheory.Measure.dirac (A.apply x w) +
    ENNReal.ofReal ε • A.uniformLaw

/-- "The positive-rate automaton obtained from `G`": the cellular automaton `G` with uniform
whole-symbol replacement at rate `ε` is a probabilistic cellular automaton with positive rates.
Spelled out as in the forgetting core's `FNE.IsPositiveRatePCA`:
(i) the deterministic rule commutes with every translation of `ℤ^d`;
(ii) it is local, with the automaton's finite neighbourhood;
(iii) given `X_0 = x`, the values `X_1(w)` are independent with laws `siteLaw x w`;
(iv) every symbol has positive probability under every `siteLaw x w` ("positive rates").
**[choice]** The phrase "positive-rate automaton" is rendered by these four clauses, as for
`FNE.CorEight`. -/
def IsPositiveRatePCA {d : ℕ} (A : UND.CA d) (ε : ℝ) : Prop :=
  (∀ (a : UND.Site d) (x : A.Config), A.apply (A.shift a x) = A.shift a (A.apply x)) ∧
  (∀ (x x' : A.Config) (w : UND.Site d), (∀ z ∈ A.nbhd, x (w + z) = x' (w + z)) →
      A.apply x w = A.apply x' w) ∧
  (∀ x : A.Config, A.law ε (MeasureTheory.Measure.dirac x) 1 =
      MeasureTheory.Measure.infinitePi (fun w => siteLaw A ε x w)) ∧
  (∀ (x : A.Config) (w : UND.Site d) (s : A.Sym), 0 < siteLaw A ε x w {s})

/-! ## Theorem A on `ℤ⁶`, and the domino reduction -/

/-- **The classical domino reduction** (R. Berger, "The undecidability of
the domino problem", Mem. Amer. Math. Soc. 66 (1966); R. M. Robinson, "Undecidability and
nonperiodicity for tilings of the plane", Invent. Math. 12 (1971), 177–209). Paper, first
sentence of `nw:machine`: "There is a total computable map `M ↦ W_M` to finite Wang sets such that
`W_M` tiles if and only if `M` does not halt." Its proof: "Use the classical effective unseeded
domino reduction of Berger and Robinson, with translations of edge-coloured squares and no
distinguished origin tile. Its output tiles precisely on the nonhalting branch."
It is the one classical input of the paper's proof of Theorem A, and the hypothesis of the
conditional form `TheoremAFromDomino`. It is also proved here for the same machine model, through
the forgetting core's family `R_M` (Theorem C): `FNR.domino_reduction` in `Reduction.lean`.
**[choice]** Machines, the blank-tape start and halting are the forgetting core's
(`FNE.TuringMachine`, `FNE.TuringMachine.Halts`), as in `FNE.CorEight`; a finite Wang set is
computed as a list of tiles, the Wang set being the set of its entries (`Finset` has no
`Primcodable` instance; as in `FNE.CorEight`); tiling is `TilesPlane` (translations only, no
distinguished origin tile). -/
def DominoReduction : Prop :=
  ∃ W : TuringMachine → List Tile, Computable W ∧
    ∀ M : TuringMachine, TilesPlane (W M).toFinset ↔ ¬ M.Halts

/-- The printed statement of **Theorem A** (introduction, `mainA`; `nw:machine`): "There is a total
computable map `M ↦ W_M` from Turing machines to finite Wang sets such that, for every
`ε ∈ (0, ε_*]`, the positive-rate automaton obtained from `G_{W_M}` is ergodic if and only if `M`
halts."
**[choice]** As in `FNE.CorEight`: a Wang set is computed as a list of tiles; computability of
`M ↦ G_{W_M}` is rendered as computability of `M ↦ W_M` (the rule `natCA` is an explicit finite
construction from the tiles); "the positive-rate automaton obtained from `G_{W_M}`" is `G_{W_M}`
with uniform whole-symbol replacement at rate `ε`, and its positive-rate property is stated
(`IsPositiveRatePCA`). -/
def ErgodicityReduction : Prop :=
  ∃ W : TuringMachine → List Tile, Computable W ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ epsStar → ∀ M : TuringMachine,
      IsPositiveRatePCA (natCA (W M).toFinset) ε ∧
        ((natCA (W M).toFinset).IsErgodic ε ↔ M.Halts)

/-- **Theorem A on `ℤ⁶`** (introduction, `mainA`; Corollary `nw:machine`), as printed: no
hypothesis. -/
def TheoremA : Prop := ErgodicityReduction

/-- Theorem A from its one classical input, the domino reduction of Berger and Robinson: the route
of the paper's proof of `nw:machine` ("The only undecidability input in this route is the
classical domino reduction of Berger and Robinson"). A conditional form, weaker than `TheoremA`;
not a printed statement. -/
def TheoremAFromDomino : Prop := DominoReduction → ErgodicityReduction

/-! ## The undecidability form (a corollary; session 1) -/

/-- **Berger's theorem (1966; Robinson 1971): the domino problem is undecidable.** "There is no
algorithm which decides, for an arbitrary finite set of Wang tiles (dominoes), whether it admits a
tiling of the plane" (translations only, no distinguished origin tile).
**[choice]** An algorithm is a computable function in Mathlib's sense; a finite Wang set is given
to it as a list of tiles (as in the forgetting core's `FNE.CorEight`: `Finset` has no
`Primcodable` instance), the Wang set being the set of its entries. -/
def DominoUndecidable : Prop :=
  ¬ ∃ g : List Tile → Bool, Computable g ∧
    ∀ l : List Tile, g l = true ↔ TilesPlane l.toFinset

/-- No algorithm decides, given `R` (as a list of tiles), whether `G_R` is ergodic at the rate
`ε`. -/
def ErgodicityUndecidable (ε : ℝ) : Prop :=
  ¬ ∃ g : List Tile → Bool, Computable g ∧
    ∀ l : List Tile, g l = true ↔ (natCA l.toFinset).IsErgodic ε

/-- **The undecidability form** (a corollary of Theorem D; the last sentence of `nw:machine`, "In
particular ergodicity is undecidable at each one of these fixed rates", for the raw inputs `R`):
under Berger's theorem, at every fixed rate `0 < ε ≤ ε_*` ergodicity of `G_R` is undecidable in
`R`. Not a printed environment; kept from session 1. -/
def TheoremAUndecidable : Prop :=
  DominoUndecidable → ∀ ε : ℝ, 0 < ε → ε ≤ epsStar → ErgodicityUndecidable ε

/-! ## Corollary `nw:machine` in full -/

/-- **Corollary `nw:machine`** (Section 3, "Theorem A on `ℤ⁶`"), its three sentences: "There is
a total computable map `M ↦ W_M` to finite Wang sets such that `W_M` tiles if and only if `M`
does not halt. For every `ε ∈ (0, ε_*]`, `G_{W_M}` with uniform replacement is a positive-rate PCA
on `ℤ⁶` that is ergodic if and only if `M` halts. In particular ergodicity is undecidable at each
one of these fixed rates."
**[choice]** As in `ErgodicityReduction`; "undecidable" for this family: no computable
`g : TuringMachine → Bool` decides whether `G_{W_M}` is ergodic at the rate `ε` (in the style of
`DominoUndecidable`). -/
def MachineCorollary : Prop :=
  ∃ W : TuringMachine → List Tile, Computable W ∧
    (∀ M : TuringMachine, TilesPlane (W M).toFinset ↔ ¬ M.Halts) ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ epsStar →
      (∀ M : TuringMachine, IsPositiveRatePCA (natCA (W M).toFinset) ε ∧
        ((natCA (W M).toFinset).IsErgodic ε ↔ M.Halts)) ∧
      ¬ ∃ g : TuringMachine → Bool, Computable g ∧
        ∀ M : TuringMachine, g M = true ↔ (natCA (W M).toFinset).IsErgodic ε

end FNR
