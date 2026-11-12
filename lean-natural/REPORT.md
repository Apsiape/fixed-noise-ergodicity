# Release package for the Lean core of the natural rule ("Forgetting under noise is undecidable", v2.0.0)

This report covers sessions 3 and 3b (12 Nov 2026). It was written by QB from the two release agents' final reports,
because the agent harness does not let subagents write REPORT.md. The underlying records are STATUS.md (decisions up to D24),
evidence/ and relay/; the session handoff note is kept in the development repository and not shipped.

## What is proved

From the frozen statement file `ForgettingNaturalRule/Statements.lean` (sha256
`3e4f73e3bc4a71ac041e45186e4d992abcd294f33ad7cfe5f4c337b8c479b5d4`, frozen in commit `386de0d`), five release targets
are proved. None of them has a hypothesis:

| Target | Type | Printed statement |
|---|---|---|
| `FNR.natural_classification` | `FNR.NaturalClassification` | Theorem D, both sentences: ergodic iff R does not tile, for every 0 < ε ≤ ε_*; if R tiles, two distinct translation-invariant stationary laws |
| `FNR.theorem_A` | `FNR.TheoremA` (= `ErgodicityReduction`) | Theorem A on ℤ⁶, unconditional reduction form |
| `FNR.machine_corollary` | `FNR.MachineCorollary` | the corollary nw:machine, all three sentences |
| `FNR.domino_reduction` | `FNR.DominoReduction` | the domino reduction: a computable W with W(M) tiling iff M does not halt |
| `FNR.domino_undecidable` | `FNR.DominoUndecidable` | undecidability of the domino problem |

The domino reduction is proved from the forgetting core's own machine family R_M: its Theorem C and Theorem B
(STATUS.md F7–F9). Berger's and Robinson's theorem is therefore not assumed. The conditional form
`FNR.theorem_A_from_domino` and `FNR.theorem_A_undecidable` stay in the development, outside the challenge; the
package audit checks their types.

## Statement fidelity

A blind fidelity read (STATEMENT-READ.md) found one mismatch: `TheoremA` named the conditional form, while the printed
Theorem A is unconditional. It also corrected one docstring (row S12: translation invariance over all of ℤ⁶ is exact,
not a choice). Both were fixed in `386de0d` before the freeze. Every other definition was read as faithful, and none
is vacuous.

## Checks (session 3b, from the public trees; session 3's run agrees)

Workspace: `/opt/forgetting-natural-rule-arxiv-2026-11-12-public` (WSL `lean-comparator`). Lean 4.35.0 (commit
`eb6cafb7`) and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

| Check | Result |
|---|---|
| Fresh serial replay, no resume | PASS: 104 modules, all exit 0, `lean -j1 -M5000`; 85 core modules (61 forgetting, 23 noise-diagram, 1 hard-model), 16 development modules, plus `Challenge`, `Solution` and `Audit`; peak process-tree memory 5.22 GB |
| `lake comparator` (bubblewrap sandbox, default kernel) | PASS on the first run: "Your solution is okay!"; `Challenge.lean` imports only Mathlib |
| leanchecker `--from-export` | PASS |
| nanoda (propext, Classical.choice, Quot.sound permitted) | PASS |
| Negative control (Classical.choice not permitted) | PASS: rejected ("unpermitted axiom Classical.choice") |
| Fresh axiom audit | PASS: 125 roots; 234 development and 6,778 core declarations; no axiom declarations; only the standard three axioms |
| Dependency sources | PASS: 10,268 sources match `pins/DEPENDENCY-SOURCES.json` |
| Census | 0 `sorry`; lint ok |

The Solution export is 310,236,705 bytes (sha256 `2b12f69f…`), byte-identical between sessions 3 and 3b.

## Vendored cores and their public sources

| Core | Source | Status |
|---|---|---|
| Forgetting v1.4.0 (`FixedNoiseErgodicity`) | `lean/` of the public release, DOI 10.5281/zenodo.24126025 | byte-identical (104 files) |
| Hard model v1.2.0 (`UndecidablePhaseDiagram`) | `lean/` of the public release, DOI 10.5281/zenodo.24144192 | byte-identical (135 files) |
| Noise diagram (`UncomputableNoiseDiagram`) | the noise-diagram Lean repository at `ec67163` (78 Lean files; identical at `d92e5f2`) | PUBLIC since 12 Nov as the `lean/` folder of noise-diagram v1.2.0 (DOI 10.5281/zenodo.24174445). QB checked all 74 Lean files there byte-identical to the committed sources (LF); README-ARXIV.md and SCOPE.md point to that DOI. |

## Not formalized

See SCOPE.md: the coalescence bound (nw:coalescence), nilpotency, the other consequences of Section 3, and the parts
of the paper already covered by the ℤ⁸ core of v1.4.0.

## Commits

`386de0d` (fidelity fix and freeze), `dac2a90` (package, evidence, relay records), `b067b44` (public re-vendor and
rerun), plus this report. Nothing has been pushed.
