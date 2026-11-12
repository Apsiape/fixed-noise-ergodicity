# Scope of the Lean formalization

This development formalizes, in Lean 4.35.0 with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`,
the natural Wang rule of S. Douglas and N. Mghirbi, "Forgetting under noise is undecidable",
version 2.0.0 (draft of 12 Nov 2026; source of record
`C:/Infanox/qb-relay-2026-10-22/opus-readback-forgetting-v2-2026-11-12/paper-fixed/`, printed numbers
from its build `work/build-readback-03`). The statements are those of the frozen statement file
`ForgettingNaturalRule/Statements.lean` (sha256 `3e4f73e3bc4a71ac041e45186e4d992abcd294f33ad7cfe5f4c337b8c479b5d4`).
The five release targets below are proved with no `sorry` and no named hypothesis, and use no axioms
beyond `propext`, `Classical.choice` and `Quot.sound`.

## Formalized, by printed number

| printed result | Lean target | type |
|---|---|---|
| **Theorem D** (introduction) = **Theorem 2.1** (`nw:classification`) without its display (9): for every finite Wang set `R` and every `0 < ε ≤ ε_*`, `G_R` with uniform whole-symbol replacement is ergodic iff `R` does not tile; if `R` tiles, two distinct translation-invariant stationary laws | `FNR.natural_classification` | `FNR.NaturalClassification` |
| **Theorem A** (introduction) = **Corollary 3.1** (`nw:machine`), second sentence, as printed, without hypothesis | `FNR.theorem_A` | `FNR.TheoremA` (`:= FNR.ErgodicityReduction`) |
| **Corollary 3.1** (`nw:machine`), all three sentences (the reduction, the ergodicity clause for the same map, undecidability at each fixed rate) | `FNR.machine_corollary` | `FNR.MachineCorollary` |
| the domino reduction of Berger and Robinson, first sentence of Corollary 3.1 (for the forgetting core's machine model) | `FNR.domino_reduction` | `FNR.DominoReduction` |
| Berger's theorem, the domino problem is undecidable (cited as [3]) | `FNR.domino_undecidable` | `FNR.DominoUndecidable` |

The proofs of Section 2 that these use are formalized along the paper's qualitative route
("Complete histories: the qualitative route"): Lemma 2.2 (`nw:budget`, reused from the noise-diagram
core), Lemma 2.3 (`nw:arms`, through the noise-diagram core's raw contours), Lemma 2.4 (`nw:sparse`, in
a weak form, F2), Lemma 2.5 (`nw:paths`, qualitative, at `ε_*`), Lemmas 2.6 and 2.7 (`nw:same`,
`nw:neighbours`, at finite age), the complete-history argument (an unmarked live reading gives a
tiling; unique complete histories give ergodicity), Lemma 2.12 (`nw:memorycover`), Lemma 2.13
(`nw:memory`) and the translation-invariant laws of Subsection "Fully translation-invariant stationary
laws" (F7). The rule, its neighbourhood and constants are displays (3)–(6). Also in the development,
outside the challenge: the conditional forms `FNR.theorem_A_from_domino : FNR.TheoremAFromDomino`
(Theorem A from the domino reduction, the route of the paper's proof) and
`FNR.theorem_A_undecidable : FNR.TheoremAUndecidable`.

## Not formalized

* The coalescence bound (9) of Theorem 2.1 (`nw:coalescence`, the all-input coefficient `q_t` of (7)),
  and what serves only it: Lemma 2.8 (`nw:forbidden`), Lemma 2.9 (`nw:mortality`), Lemma 2.10
  (`nw:allinput`), the quantitative estimates (15), (16) and (20) in their printed forms (Lemma 2.4 is
  proved in a weak form; Lemma 2.5 only qualitatively; the uniqueness and attraction of Lemma 2.11 are
  proved by the qualitative route, not its estimate).
* Corollary 3.2 (`nw:nilpotent`, nilpotency).
* Every other consequence of Section 3: Corollary 3.3 (Gibbs uniqueness and weak spatial mixing),
  Remark 3.4, Corollary 3.5 (a uniform radius), Remark 3.6, Corollary 3.7 (completeness at a fixed
  rational rate), Corollary 3.8 (replacement values), Corollary 3.9 (no total forgetting-time bound),
  Theorem 3.10 (an extreme phase for each tiling), Corollary 3.11 (the `ℤ⁷` stack) and Remark 3.12.
* The inspector theory, Sections 4–6 (Theorem B = Theorems 5.1 and 6.2), and the machine-family
  route, Sections 7–11 (Theorem C = Theorems 9.8 and 11.1, the machine-family Theorem 10.2 and
  Corollary 11.21 on `ℤ⁸`): whatever of them is formalized is the old `ℤ⁸` core's (the forgetting
  core, release v1.4.0, DOI 10.5281/zenodo.24126025). This development imports that core and uses
  two of its theorems (Theorem C for the family `R_M`, and the non-computability of halting) to prove
  the domino reduction; it does not re-claim or extend that core's scope.
* Section 12, "Lower dimensions" (the saturation theorem, the all-path density lemma, the natural rule on `ℤ⁴`,
  Theorem 12.5 = Theorem E, and the deterministic-tile family on `ℤ³`, Theorem 12.11 = Theorem F), Section 13 (open
  problems), the sections after it, and the Appendices A–C.

## Proof-route differences (the statements are as printed; `STATUS.md`, F1–F9)

* **F1.** The non-tiling direction follows the qualitative complete-history route (the noise-diagram
  core's Lemma 8.5 for ergodicity), not the quantitative forbidden-square route (Lemmas 2.8–2.11). The
  tiling is read off directly from the coherent letters of a complete history.
* **F2.** Sparse roots in a weak form: `P(v ∈ 𝓜) ≤ Σ_{f≥1}(K_c ε)^f ≤ 1/4` instead of `< 2ε`; the
  memory gap is `1/2` instead of `1 - 4ε`. Enough for non-ergodicity and for the two laws.
* **F3.** The coherence induction uses the uniform age condition `s + d < t` for the displacements
  `0, e₁, e₂`; it is applied to complete trajectories, where any age is available.
* **F4.** The marked field is the noise-diagram core's raw marked set, literally the paper's (11); its
  contour, packing and counting lemmas are reused, with base `K_c ε ≤ 1/8`. Only the qualitative
  consequence (no infinite marked path almost surely) is formalized.
* **F5.** The memory branch evolves both starts with two-sided noise from time `0`, identified with
  the one-sided process.
* **F6.** Non-ergodicity is obtained from memory between two Dirac starts; the translation-invariant
  laws are a separate clause.
* **F7.** The translation-invariant laws exchange the paper's two averages: temporal Cesàro limits
  first (stationary laws with the one-site bounds at every site), then one-dimensional spatial
  averages along the six coordinate directions in turn. No averaging over squares, tiling space or
  boundary count is needed.
* **F8.** The domino reduction is proved with the forgetting core's family `R_M` (Theorem C), not with
  Berger's or Robinson's construction; the statement does not name the construction.
* **F9.** "Refutable ⇒ not tiling" for `R_M` is obtained from the forgetting core's Theorem B at its
  rate `ε₀` (ergodic when `M` halts, non-ergodic when `R_M` tiles), not from a combinatorial lemma.

## Precedent cores reused

All three are on the same pins. The release package vendors them as sources under `vendor/` and
compiles from source exactly the modules this development imports (61 of the forgetting core, 1 of
the hard-model core, 23 of the noise-diagram core; `evidence/BUILD.json`). The forgetting and
hard-model trees are the `lean/` folders of their public releases, byte for byte; the noise-diagram
tree is its release package, whose Lean sources are byte-identical to the `lean/` folder of its public release v1.2.0 (DOI 10.5281/zenodo.24174445). Each rebuilt object is compared byte for
byte with the one built in that core's verification workspace (`evidence/VENDOR-CORES.json`).

* **The forgetting core** `FixedNoiseErgodicity` (the old `ℤ⁸` core; "Forgetting under noise is
  undecidable" v1.4.0, DOI 10.5281/zenodo.24126025), vendored whole from the `lean/` folder of that
  public release. Statement level: `FNE.Tile`, `FNE.WangSet`, `FNE.Plane`,
  `FNE.TuringMachine`, `FNE.TuringMachine.Halts`, `FNE.flagLaw`, `FNE.WeakTendsto`. Proofs: Theorem C
  (`FNE.Family.familyR`, `FNE.Family.computable_familyR`, `FNE.Family.tiles_of_not_halts`,
  `FNE.Three.eight_familyR`), `FNE.not_ergodic_of_tiles`, `FNE.halts_not_computable`, and the Section 2
  process and edge-count layers (through the noise-diagram core).
* **The hard-model core** `UndecidablePhaseDiagram` ("An uncomputable phase diagram at positive
  temperature for one classical lattice model" v1.2.0, DOI 10.5281/zenodo.24144192), vendored from
  the `lean/` folder of that public release; reached only through the noise-diagram core.
* **The noise-diagram core** `UncomputableNoiseDiagram` ("One noisy cellular automaton with an
  uncomputable noise diagram" v1.1.0, DOI 10.5281/zenodo.24152233; its Lean release package of
  12 Nov 2026, not yet public: the v1.1.0 release has no `lean/` folder), vendored from
  `/opt/uncomputable-noise-diagram-arxiv-2026-11-12`. Statement level:
  `UND.Site`, `UND.CA` with its process, laws, stationarity, ergodicity, translates and
  `UND.CA.HasTwoTIStationaryLaws`. Proofs: the PCA layer (`law_map_shift`, `integral_law`, `PhiBCF`,
  `exists_cesaro_limit`, `ergodic_of_unique`, `not_ergodic_of_memoryFrom`), the raw marked set and its
  contour, packing and path lemmas (its Lemmas 5.1–5.3), and the audit command.
