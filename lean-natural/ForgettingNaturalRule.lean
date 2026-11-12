/-
# Root module

Lean formalization of the core of S. Douglas and N. Mghirbi, "Forgetting under noise is
undecidable", version 2.0.0 (draft of 12 Nov 2026): the natural Wang rule on `ℤ⁶`.

* `Statements.lean` (FROZEN, session 3; sha256 in `STATUS.md`): `FNR.NaturalClassification`
  (Theorem D: the ergodicity classification and the two translation-invariant stationary laws on
  tilers), `FNR.TheoremA` (Theorem A on `ℤ⁶`, as printed, without hypothesis), the domino
  reduction of Berger and Robinson `FNR.DominoReduction`, Theorem A from it
  `FNR.TheoremAFromDomino` (a conditional form), Corollary `nw:machine` `FNR.MachineCorollary`,
  the undecidability form `FNR.TheoremAUndecidable`, and every definition they use;
* `Main.lean`: `FNR.natural_classification`, `FNR.theorem_A_from_domino`,
  `FNR.theorem_A_undecidable`;
* `Reduction.lean`: the domino reduction proved from the forgetting core's Theorem C
  (`FNR.domino_reduction`), hence, without hypothesis, `FNR.theorem_A` (= `FNR.ergodicity_reduction`),
  `FNR.domino_undecidable`, `FNR.ergodicity_undecidable` and `FNR.machine_corollary`;
* `Constants.lean`: `Δ = 18q`, `B = 2Δ²`, `K_c = 4B^{101}`, `ε_* = B^{-200}`, `K_c ε ≤ 1/8`;
* `Rule/Local.lean`: the rule `GI` on `ℤ² × ℤ⁴`, quorum uniqueness, locality, the references;
* `Rule/Bridge.lean`: the statement's automaton `natCA R` is `GI`; trajectories;
* `Coherence/Rel.lean`: Lemmas `nw:budget`, `nw:same`, `nw:neighbours` (finite age);
* `Coherence/Tiling.lean`: complete histories, an unmarked live reading gives a tiling;
* `Forget/Paths.lean`: Lemmas `nw:paths` (qualitative) and `nw:sparse` (weak) at `ε_*`;
* `Forget/Unique.lean`: unique complete histories, the forgetting branch;
* `Memory/Cover.lean`: Lemma `nw:memorycover`;
* `Memory/Branch.lean`: Lemma `nw:memory`, the memory branch;
* `PCA/Average.lean`: spatial averages of stationary laws (generic PCA layer);
* `Memory/Invariant.lean`: two translation-invariant stationary laws on tilers.

Reused (read-only imports): the noise-diagram core (`UncomputableNoiseDiagram`, its statement
layer, PCA layer, raw marked set, contour and path lemmas) and, through it, the forgetting core
(`FixedNoiseErgodicity`) and the hard-model core (`UndecidablePhaseDiagram`); `Reduction.lean`
imports the whole forgetting core.
-/
import ForgettingNaturalRule.Statements
import ForgettingNaturalRule.Constants
import ForgettingNaturalRule.Rule.Local
import ForgettingNaturalRule.Rule.Bridge
import ForgettingNaturalRule.Coherence.Rel
import ForgettingNaturalRule.Coherence.Tiling
import ForgettingNaturalRule.Forget.Paths
import ForgettingNaturalRule.Forget.Unique
import ForgettingNaturalRule.Memory.Cover
import ForgettingNaturalRule.Memory.Branch
import ForgettingNaturalRule.PCA.Average
import ForgettingNaturalRule.Memory.Invariant
import ForgettingNaturalRule.Main
import ForgettingNaturalRule.Reduction

set_option autoImplicit false
