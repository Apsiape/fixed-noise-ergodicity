# Scope of the Z4 Lean formalization

This package checks the natural raw-Wang rule on Z4, Theorem 12.5 (`ld:z4`) of
S. Douglas and N. Mghirbi, *Forgetting under noise is undecidable*, v2.0.0,
retained in v2.1.0. The statement of record is the frozen
`ForgettingLower/Statements.lean`, SHA256
`58cb7388400f05f2986d2b2cc9154a99a554eed4b384f10c8809b706d3b244c4`.
The proof source commit is `321e81225e73db9311a6c871057b513bfa020a9f`.
Packaging changes no original Lean source and adds no mathematics.

## Formalized

| Printed statement | Lean theorem | Exact frozen type |
|---|---|---|
| Theorem 12.5 (`ld:z4`), every sentence: one common neighbourhood; for every finite raw Wang set R and every 0 < e <= e0, ergodicity iff R does not tile; tiling gives two distinct invariant probability laws; non-tiling gives finite-window coupling from the past and weak convergence from every initial probability law to the unique invariant law | `FLD.z4_classification` | `FLD.Z4Classification` |
| Direct machine corollary: one computable machine-to-tile-list map W, its domino specification, positive rates, ergodicity iff halting for every allowed rate, and no computable ergodicity decider on this machine family | `FLD.z4_machine_corollary` | `FLD.Z4MachineCorollary` |
| The raw-family fixed-rate undecidability sentence, for every allowed rate and therefore at the explicit positive rational rate e0 | `FLD.z4_raw_undecidable` | `FLD.Z4RawUndecidable` |

The constants and rule are transparent and uniform in R: K = 16^2, q = 768,
h = 512, S0 = {0,...,15}^2, S1 = 160 e1 + S0, S2 = 160 e2 + S0, and
e0 = 382205952^(-33720). The alphabet is the raw tile set plus blank. The checker
uses the five cardinal readings and the quorum uses all 768 providers; the common
neighbourhood is Gamma times S. Noise is uniform whole-symbol replacement.
Ergodicity, invariance, probability laws and weak convergence use the precedent
cores' definitions. None of the three target types has a named hypothesis.

`AllTimeCFTP` puts all integer observation times and finite windows inside one
almost-sure quantifier, uniformly over initial configurations and all sufficiently
long horizons. This is an equivalent addition beyond the printed words, as the
blind read records. The machine corollary strengthens the printed final sentence
by covering all allowed rates, the machine-indexed family and positive rates.
The separate raw-family proposition was added before the freeze (ruling R1).
`STATEMENT-READ.md` preserves the blind read and records the pre-freeze R1-R3 changes.

The proofs include the three-box contour and all-path density machinery, the
amortized same-site coherence, separate planar edge matching and extraction,
uniqueness of complete histories, CFTP, and the memory construction of two
stationary probability laws. The machine corollary uses the already proved,
unconditional `FNR.domino_reduction`; no domino hypothesis is introduced.

## Proof-route differences

- A tiling is extracted directly from coherent readings in a complete history;
  separate east and north matching establish its edges.
- Sparse roots are bounded by 1/4 and the memory gap by 1/2. The printed
  intermediate bound < 2e and gap 1 - 4e are not claimed. These weaker bounds
  suffice for exactly the frozen qualitative classification.
- All-time CFTP follows by deterministic time translation from all-time
  complete-history uniqueness on one probability-one event.
- The two invariant laws are temporal Cesaro limits. The frozen Z4 statement
  adds no spatial translation-invariance condition.

## Not formalized by this package

- Theorem 12.11 (`ld:z3`), the Z3 deterministic-tile family, Kari's theorem or
  any Z3 stretch result.
- Theorem 12.12 of v2.1.0, its exponential convergence rate, effective prefactor,
  all-input nonconstancy estimate or any quantitative rate on Z4 or Z3.
- The saturation theorem, the printed quantitative intermediate estimates not
  stated above, Gibbs consequences, or any other result outside these three
  frozen target propositions. Auxiliary lemmas used in their proofs do not
  extend the release claim to other printed statements.
- New claims about the precedent papers. Their earlier formalizations are
  reused as public source dependencies with their existing scope.

## Public source dependencies

All four cores are vendored whole from public release folders and compiled from
source for exactly the imported modules. `evidence/VENDOR-CORES.json` records each
file's public and vendored digest. No precedent object is reused for those cores.

| Core | Public folder | Release / DOI |
|---|---|---|
| `ForgettingNaturalRule` | `fixed-noise-ergodicity` / `lean-natural/` | v2.1.0, 10.5281/zenodo.24178276; tree identical to v2.0.0 |
| `FixedNoiseErgodicity` | same release / `lean/` | v2.1.0, 10.5281/zenodo.24178276 |
| `UncomputableNoiseDiagram` | `uncomputable-noise-diagram` / `lean/` | v1.3.0, 10.5281/zenodo.24178271 |
| `UndecidablePhaseDiagram` | `undecidable-phase-diagram` / `lean/` | v1.2.0, 10.5281/zenodo.24144192 |

Lean is pinned to 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), Mathlib to
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The nine pinned dependency packages
use prebuilt objects; their source files are checked against the public dependency
manifest. Independent kernel checks apply to the exported proof closure.
