# Lean formalization: the natural rule on ℤ⁶ and Theorem A on ℤ⁶

This directory proves, in Lean 4 with Mathlib, the natural-rule theorem of version 2.0.0 of "Forgetting under noise is undecidable" (Theorem D = Theorem 2.1, both sentences, without its coalescence bound) and Theorem A on ℤ⁶ (all of Corollary 3.1), together with the domino reduction and the undecidability of the domino problem. The proofs contain no `sorry`, take no named hypotheses, and use no axioms beyond Lean's three standard axioms `propext`, `Classical.choice` and `Quot.sound`. Appendix C of the paper describes the formalization. The older machine-family core on ℤ⁸ is in `../lean/`.

## Reproduce

Install the toolchain specified by `lean-toolchain` (Lean 4.35.0), and have Git and Mathlib's cache prerequisites available. From this directory run:

```sh
export LEAN_NUM_THREADS=1
lake exe cache get
lake build
lake env lean -j1 -M5000 Audit.lean
```

The cache command fetches the pinned Git dependencies and Mathlib's standard build cache. Plain `lake build` compiles the entire `ForgettingNaturalRule` library from the shipped sources. Compare the audit's axiom lines with `AXIOMS.txt`; this paper's recorded hypothesis policy in the evidence and statement files remains authoritative. Named hypotheses are preserved. The standard build does not run the comparator, the custom Python replay, or independent kernel replays, and does not rewrite `AXIOMS.txt`.

The recorded root `AXIOMS.txt` has 143 axiom diagnostic lines; the unchanged release `Audit.lean` emits 250 because it pairs `#print axioms` with `#audit_axioms_strict` for every root. The named-root-to-axiom-set comparison is identical for all 125 roots, with no added or missing root or changed axiom set. For a direct normalized-line comparison of the complete release diagnostics, use the unchanged `evidence/AXIOMS.txt`, which matches the standard test output. Both original reference files are retained.

Allow at least 8 GiB of available physical memory and run one Lean compiler process on the machine at a time. The package passes `-j1 -M5000`. On PowerShell set `$env:LEAN_NUM_THREADS = '1'`. Compiler thread limits do not provide a machine-wide process lock: serialize launches externally and check memory before building. This toolchain's Lake has no `lake build -j1` option.

Mathlib is required by Git at `56a005855ea17e0b0958f73ec801ae140b0a1679`; the Lake-generated manifest pins its eight inherited dependencies to the recorded revisions. Use the shipped manifest; ordinary reproduction does not require `lake update`. The stock Mathlib cache tool is used without the historical override.

`Challenge.lean`, `Solution.lean`, and `Audit.lean` are ordinary files checked with `lake env lean -j1 -M5000 FILE.lean`. Challenge retains its intentional comparator holes and is excluded from the library. Library and final audit output must have no `declaration uses sorry` warnings.

The reused cores are real local Lake packages in `deps/`, declared with `require <Core> from "deps/<Core>"`. Only each consumer's recorded import closure is shipped, byte for byte. All packages share the same pinned Mathlib; no cross-repository source path or Git core dependency is needed.

`UPDStatements` is a separate library with only `UndecidablePhaseDiagram.Statements` as its root. It supplies `-Dbackward.isDefEq.respectTransparency=false` for the unchanged Lean 4.35 `Fintype` derivations. Other modules retain their original elaboration options. The two UPD libraries together cover exactly the original module set (or the consuming package's recorded subset).

The Python replay, evidence, and previous reproduction instructions below are retained as optional historical tools. They assume the old `vendor/` layout, prebuilt objects, and in some cases a host-memory heartbeat; plain `lake build` does not invoke them. Run any historical preparation in a separate copy and retain the standard manifest in this one. Historical checks describe the original release, not new comparator or kernel replays by the standard build.

## What is proved

`ForgettingNaturalRule/Statements.lean` defines, transparently and with no proofs of substance, every object in the statements, and states them as propositions. It was read against the paper by a model that did not write it (`STATEMENT-READ.md`), then frozen. The proofs are in `ForgettingNaturalRule/Main.lean` and the modules it imports.

| Printed result | Lean name |
|---|---|
| Theorem D (Theorem 2.1): for every finite Wang set R and every 0 < ε ≤ ε_*, the noisy rule G_R on ℤ⁶ is ergodic iff R does not tile the plane; if R tiles, there are two distinct translation-invariant stationary laws | `FNR.natural_classification : FNR.NaturalClassification` |
| Theorem A on ℤ⁶: a total computable map M ↦ W_M with G_{W_M} ergodic at every rate in (0, ε_*] iff M halts | `FNR.theorem_A : FNR.TheoremA` |
| Corollary 3.1, all three sentences | `FNR.machine_corollary : FNR.MachineCorollary` |
| The domino reduction: a computable map M ↦ W_M with W_M tiling iff M does not halt | `FNR.domino_reduction : FNR.DominoReduction` |
| The domino problem is undecidable | `FNR.domino_undecidable : FNR.DominoUndecidable` |

The domino reduction is proved from the paper's own machine family R_M (its Theorems B and C, formalized in the ℤ⁸ core), so Berger's and Robinson's theorem is not assumed. `SCOPE.md` lists exactly what is and is not formalized. Not formalized: the coalescence bound, nilpotency, the other consequences of Section 3, and the lower-dimensional theorems of Section 12 (ℤ⁴ and ℤ³).

## Checks

- **Pins:** Lean 4.35.0 (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- **Comparator:** `Challenge.lean` imports only Mathlib and states the five targets as holes. `comparator.json` permits only the three standard axioms. The sandboxed `lake comparator` run accepted `Solution.lean`.
- **Kernel replays:** two independent kernels, leanchecker and nanoda, replayed the exported proof closure. A negative control, nanoda without `Classical.choice` permitted, was rejected as expected.
- **Axiom audit:** `Audit.lean` checks the axioms of every declaration of the development and of the imported core modules; the result is in `AXIOMS.txt`.
- **Records:** `REPORT.md` gives the full results, `evidence/` the machine-readable records, and `relay/` the run logs.

## Reused cores

The package compiles the needed modules of three earlier cores from their public sources:
- the ℤ⁸ machine-family core: the `lean/` folder of version 1.4.0 of this paper, DOI [10.5281/zenodo.24126025](https://doi.org/10.5281/zenodo.24126025);
- the noise-diagram core: the `lean/` folder of version 1.2.0 of "One noisy cellular automaton with an uncomputable noise diagram", DOI [10.5281/zenodo.24174445](https://doi.org/10.5281/zenodo.24174445);
- the hard-model core: the `lean/` folder of version 1.2.0 of "An uncomputable phase diagram at positive temperature for one classical lattice model", DOI [10.5281/zenodo.24144192](https://doi.org/10.5281/zenodo.24144192).

## Historical reproduction workflow (optional)
`README-ARXIV.md` gives the recorded setup and commands, run on a Linux (WSL) workspace. The Mathlib dependencies and the three reused cores are placed under `vendor/` as path packages; they are fetched, not shipped. `scripts/replay.py` compiles the needed core modules, the development, `Challenge`, `Solution` and `Audit`, one process at a time.

## License

See `RIGHTS.md` at the repository root.
