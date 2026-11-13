/-
# Statement file — FROZEN (12 Nov 2026): Section 12, Theorem 12.5 (ld:z4), v2.0.0

Frozen after the blind fidelity read and QB rulings of 12 Nov 2026.
The sha256 in STATUS.md is the statement of record; this file never changes again.
Source: fixed-noise-ergodicity-release/paper/sections/12-lower-dimensions.tex.

REUSE: FNE.Tile/WangSet/Plane/TuringMachine/Halts, FNR.TilesPlane and Letter,
UND.CA (including the actual uniform whole-symbol noise, probability laws,
IsStationary, IsErgodic and FNE.WeakTendsto), FNR.IsPositiveRatePCA.
ADAPT: the transparent FNR cardinal-checker/quorum construction, with two
transverse coordinates, three boxes and h = 512. The first two coordinates
of UND.Site 4 are planar. Option (Fin 2) indexes clusters 0,1,2.

Only target propositions are stated here; their proofs live in the proof files.
**[choice]** Inherited encodings (natural-number tile colours, list-coded raw inputs,
the FNE machine model and UND noise time indexing) are reused verbatim from the frozen cores.
-/
import ForgettingNaturalRule.Statements

set_option autoImplicit false

noncomputable section

namespace FLD

open FNE (Tile WangSet Plane TuringMachine)
open MeasureTheory

/-- Tiling with translations only, no distinguished tile; exactly FNR's predicate.
**[choice]** Reuse its map-to-tiles encoding with membership in R. -/
abbrev TilesPlane := FNR.TilesPlane

/-- ld:constants: one cluster contains K = 16² offsets. -/
def K : ℕ := 16 ^ 2
/-- ld:constants: three clusters. -/
def q : ℕ := 3 * K
/-- Bound on the undirected ordinary degree, using |Λ| = 9. -/
def Delta : ℕ := 18 * q
/-- The connected-edge encoding base 2Δ². -/
def B : ℕ := 2 * Delta ^ 2
/-- The transverse l1 diameter of S. -/
def D : ℕ := 350
/-- The all-path marked-parent density cutoff. -/
def delta : ℝ := 1 / (4 * ((D : ℝ) + 1))
/-- Integer cost per flag of the whole path, spurs and contours. -/
def densityCost : ℕ := 16860
/-- The single rational rate, independent of R. -/
def eps0Rat : ℚ := ((382205952 : ℚ) ^ 33720)⁻¹
/-- ld:constants: e₀ = 382205952^(-33720), exactly as printed. -/
def eps0 : ℝ := ((382205952 : ℝ) ^ 33720)⁻¹

/- The following definitions adapt FNR's statement definitions. `site` is
(u₁,u₂,P₁,P₂); `corner none = 0`, `corner (some j) = 160 e_j`;
Provider indexes S₀ ⊔ S₁ ⊔ S₂, and offset is corner + {0,...,15}².
Keeps checks all five live cardinal letters and the four oriented edges.
check keeps the central tile iff Keeps holds. natMap takes a live quorum
of 512 votes, or blank. natNbhd = Γ × S is independent of R.
letterEquiv reuses the existing alphabet bijection. natCA evaluates the
rule on its neighbourhood; the extension by blank is immaterial by locality.
-/
/-- Section 12: site (u,P) in Z4.
**[choice]** The planar coordinates come first. -/
def site (u : Plane) (P : Fin 2 → ℤ) : UND.Site 4 :=
  Fin.cons (α := fun _ => ℤ) u.1 (Fin.cons (α := fun _ => ℤ) u.2 P)

/-! ## The three provider boxes (Section 12, ld:constants) -/

/-- ld:constants: the corners 0, 160e1, 160e2.
**[choice]** Option (Fin 2) labels clusters: none is 0, some 0 is 1, some 1 is 2. -/
def corner : Option (Fin 2) → (Fin 2 → ℤ)
  | none => 0
  | some i => fun j => if j = i then 160 else 0

/-- Three indexed boxes, each with 16 squared offsets. -/
abbrev Provider := Option (Fin 2) × (Fin 2 → Fin 16)

/-- The physical provider offset in its indexed box. -/
def offset (π : Provider) : Fin 2 → ℤ := corner π.1 + fun j => ((π.2 j : ℕ) : ℤ)

/-- The explicit finite box S_c = corner c + {0,...,15} squared. -/
def providerBox (c : Option (Fin 2)) : Finset (Fin 2 → ℤ) :=
  (Finset.univ : Finset (Fin 2 → Fin 16)).image fun o => offset (c, o)
/-- S0 = {0,...,15} squared. -/
def S0 : Finset (Fin 2 → ℤ) := providerBox none
/-- S1 = 160e1 + S0. -/
def S1 : Finset (Fin 2 → ℤ) := providerBox (some 0)
/-- S2 = 160e2 + S0. -/
def S2 : Finset (Fin 2 → ℤ) := providerBox (some 1)
/-- The union of all three provider boxes, indexed by Provider. -/
def S : Finset (Fin 2 → ℤ) := (Finset.univ : Finset Provider).image offset

/-! ## The alphabet and cardinal checker (Section 12, natural rule) -/

abbrev Letter (R : WangSet) := FNR.Letter R

/-- Section 12: five live cardinal readings with matching shared edges. -/
def Keeps {R : WangSet} (x : UND.Site 4 → Letter R) (v : UND.Site 4) (c : R) : Prop :=
  x v = some c ∧
    (∃ b : R, x (v + site (1, 0) 0) = some b ∧ c.1.E = b.1.W) ∧
    (∃ b : R, x (v + site (-1, 0) 0) = some b ∧ b.1.E = c.1.W) ∧
    (∃ b : R, x (v + site (0, 1) 0) = some b ∧ c.1.N = b.1.S) ∧
    (∃ b : R, x (v + site (0, -1) 0) = some b ∧ b.1.N = c.1.S)

open Classical in
/-- Section 12: keep the centre exactly when its cardinal check passes. -/
def check {R : WangSet} (x : UND.Site 4 → Letter R) (v : UND.Site 4) : Letter R :=
  if ∃ c, Keeps x v c then x v else none

/-- The number of checked providers voting for a specified live tile. -/
def votes {R : WangSet} (x : UND.Site 4 → Letter R) (v : UND.Site 4) (s : R) : ℕ :=
  (Finset.univ.filter fun π : Provider => check x (v + site 0 (offset π)) = some s).card

/-- ld:constants: h = 2K = 512. -/
def quorum : ℕ := 2 * 16 ^ 2

open Classical in
/-- G_R^(4): the unique live quorum tile if present, otherwise blank.
**[choice]** Classical.choose selects the tile; 2 * 512 > 768 makes it unique. -/
def natMap (R : WangSet) (x : UND.Site 4 → Letter R) : UND.Site 4 → Letter R := fun v =>
  if h : ∃ s : R, quorum ≤ votes x v s then some h.choose else none

/-! ## The automaton `G_R` on `ℤ⁴` -/

abbrev cardinal : Finset Plane := FNR.cardinal

/-- Section 12: the common neighbourhood Gamma times S. -/
def natNbhd : Finset (UND.Site 4) :=
  (cardinal ×ˢ (Finset.univ : Finset Provider)).image fun p => site p.1 (offset p.2)

/-- Reuse FNR's bijection from R plus blank to the finite symbol alphabet.
**[choice]** Fintype.equivFin relabels Option R as Fin |Option R|. -/
def letterEquiv (R : WangSet) : Letter R ≃ Fin (Fintype.card (Letter R)) :=
  FNR.letterEquiv R

/-- The explicit Z4 automaton, evaluated through its finite neighbourhood.
**[choice]** Extend the pattern by blank outside natNbhd; those values are never read. -/
def natCA (R : WangSet) : UND.CA 4 where
  numSymbols := Fintype.card (Letter R)
  numSymbols_pos := Fintype.card_pos
  nbhd := natNbhd
  localRule pat := letterEquiv R (natMap R (fun z =>
    if h : z ∈ natNbhd then (letterEquiv R).symm (pat ⟨z, h⟩) else none) 0)


/-- Exactly the printed two distinct invariant probability laws; no spatial
translation-invariance condition is added to Theorem 12.5. -/
def HasTwoInvariantLaws {d : ℕ} (A : UND.CA d) (e : ℝ) : Prop :=
  ∃ μ ν : Measure A.Config, μ ≠ ν ∧
    IsProbabilityMeasure μ ∧ A.IsStationary e μ ∧
    IsProbabilityMeasure ν ∧ A.IsStationary e ν

/-- Finite-window coupling from the past, simultaneously for all finite windows,
all observation times, all sufficiently remote past horizons and all starts.
This uses UND.CA.flow and the existing two-sided iid noise measure verbatim.
**[choice]** The added forall t is equivalent to the printed per-window form
by countability of the time and finite-window index sets; it goes beyond the printed words. -/
def AllTimeCFTP {d : ℕ} (A : UND.CA d) (e : ℝ) : Prop :=
  ∀ᵐ ω ∂(A.noiseLaw₂ e), ∀ t : ℤ, ∀ O : Finset (UND.Site d),
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x y : A.Config, ∀ w ∈ O,
      A.flow ω (t - (n : ℤ)) n x w = A.flow ω (t - (n : ℤ)) n y w

/-- Theorem 12.5 (ld:z4), every sentence. IsErgodic already states existence
and uniqueness of an invariant probability law AND weak convergence from every
initial probability law. The non-tiling clause repeats it next to CFTP so that
this printed sentence remains explicit. Constants and natNbhd are global
transparent definitions independent of R; the common-neighbourhood clause is
included literally. No convergence rate or Gibbs consequence is asserted.
**[choice]** Ergodicity is repeated in the non-tiling clause to retain that printed sentence. -/
def Z4Classification : Prop :=
  (∀ R : WangSet, (natCA R).nbhd = natNbhd) ∧
  ∀ (R : WangSet) (e : ℝ), 0 < e → e ≤ eps0 →
    ((natCA R).IsErgodic e ↔ ¬ TilesPlane R) ∧
    (TilesPlane R → HasTwoInvariantLaws (natCA R) e) ∧
    (¬ TilesPlane R → AllTimeCFTP (natCA R) e ∧ (natCA R).IsErgodic e)

/-- The direct Z⁴ undecidability corollary. Same computable W for all allowed
rates, with its domino specification, positive-rate property, classification,
and no computable decider at any one fixed allowed rate. Machines and list
codes are exactly FNR's, so FNR.domino_reduction applies with no hypotheses.
**[choice]** This strengthens the printed last sentence: every allowed rate,
the machine-indexed subfamily and a positive-rate clause. It implies Z4RawUndecidable. -/
def Z4MachineCorollary : Prop :=
  ∃ W : TuringMachine → List Tile, Computable W ∧
    (∀ M : TuringMachine, TilesPlane (W M).toFinset ↔ ¬ M.Halts) ∧
    ∀ e : ℝ, 0 < e → e ≤ eps0 →
      (∀ M : TuringMachine, FNR.IsPositiveRatePCA (natCA (W M).toFinset) e ∧
        ((natCA (W M).toFinset).IsErgodic e ↔ M.Halts)) ∧
      ¬ ∃ g : TuringMachine → Bool, Computable g ∧
        ∀ M : TuringMachine, g M = true ↔ (natCA (W M).toFinset).IsErgodic e

/-- Proof of Theorem 12.5, last sentence: fixed-rate undecidability on the raw family
R ↦ G_R^(4) (abstract: "one explicit positive rational replacement rate ... makes ergodicity
undecidable"). Raw inputs are lists of tiles, as in FNR.ErgodicityUndecidable; no hypothesis. -/
def Z4RawUndecidable : Prop :=
  ∀ e : ℝ, 0 < e → e ≤ eps0 →
    ¬ ∃ g : List Tile → Bool, Computable g ∧
      ∀ l : List Tile, g l = true ↔ (natCA l.toFinset).IsErgodic e

end FLD
