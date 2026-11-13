# Z4 Lean release verification report — 12 Nov 2026

The release package passes all requested checks. It checks precisely
`FLD.z4_classification : FLD.Z4Classification`,
`FLD.z4_machine_corollary : FLD.Z4MachineCorollary`, and
`FLD.z4_raw_undecidable : FLD.Z4RawUndecidable`, with no named hypotheses.
`SCOPE.md` gives the exact claim and exclusions; `STATEMENT-READ.md` preserves
the blind read and records that R1-R3 were applied before the freeze.

Proof source: `321e81225e73db9311a6c871057b513bfa020a9f`; freeze: `eb00b98`.
The packaging commit is the commit containing this report (`git log -1`).
No original Lean source changed, and no mathematics was added. Statements.lean
remains frozen at SHA256 `58cb7388400f05f2986d2b2cc9154a99a554eed4b384f10c8809b706d3b244c4`.
Nothing was pushed or published; no installation, network fetch or outside
contact occurred. No subagents were used.

## Checks

| Check | Result |
|---|---|
| Fresh serial replay, no resume | PASS: 133 modules; 31 Z4, 99 precedent-core, and 3 package modules; every exit 0 |
| Challenge reachable-constant pre-check | PASS: 116 development constants equal 116 challenge constants, including kinds, type hashes and definition-value hashes |
| Actual `lake comparator --config comparator.json` | PASS: bubblewrap sandbox, default kernel, no supplied export; “Your solution is okay!” |
| Solution export | PASS: 310,204,729 bytes, SHA256 `8beb8c9a9b88a935c2c475b053b45c1e4bd52581c277e471e1f5cd70db7bbebb` |
| `leanchecker --from-export` | PASS |
| `nanoda_bin`, propext / Classical.choice / Quot.sound | PASS |
| Negative control without Classical.choice | PASS: rejected for `unpermitted axiom "Classical.choice"` |
| Fresh axiom audit | PASS: 206 strict roots, 464 Z4 declarations and 7009 imported core declarations; generated and private declarations included; only the standard three axioms |
| Pinned dependency source check | PASS: 10,268 source files checked against the public manifest |
| Development census / source audit | PASS: 0 holes in 31 original Lean files; exactly three intended Challenge holes; forbidden constructs none; autoImplicit false; lint PASS |
| Frozen statement and original Lean source identity | PASS: Windows and WSL agree; all 31 original Lean files unchanged |
| Final process cleanup | PASS: no Lean tools remain; owned host-memory monitor stopped; no process killed |

The precedent module split is FixedNoiseErgodicity: 61, UndecidablePhaseDiagram: 1, UncomputableNoiseDiagram: 23, ForgettingNaturalRule: 14. Every compile used the copied guards,
`lean -j1 -M5000`, one thread, >=8 GiB available, a per-module timeout, and the
9.0 GB process-tree watchdog. Fresh replay peak tree RSS was
5.225 GB; minimum available before a compile
was 10.91 GiB.
The original Z4 modules have zero warnings. Unchanged public predecessor sources
emit existing warnings; the three Challenge holes emit their expected warnings.
The complete warning counts and commands are retained in `evidence/BUILD.json`.

## Vendored public-tree identity

| Core | Files compared | Result |
|---|---:|---|
| ForgettingNaturalRule | 93 | PASS |
| FixedNoiseErgodicity | 104 | PASS |
| UncomputableNoiseDiagram | 166 | PASS |
| UndecidablePhaseDiagram | 135 | PASS |

Each comparison is file by file, byte for byte, including non-Lean files.
Public git blobs also match the release working folders and their SHA256SUMS.
The natural-rule `lean-natural/` tree in forgetting v2.1.0 is identical to v2.0.0.
The four sources are exactly those requested in PACKAGE-2026-11-12.md; no private
development or relay tree is substituted for a public source folder.
The nine pinned packages use prebuilt objects; their source files are verified,
and the independent kernels replay the exported proof closure.

## Records and reproduction

WSL workspace: `/opt/forgetting-lower-arxiv-2026-11-12` in `lean-comparator`.
`project/` began as git archive of the exact proof commit plus package files.
The four core trees and nine dependencies are under `project/vendor/`.
No core or development object was reused in the fresh replay. The toolchain,
bubblewrap and nine pinned dependencies were copied from read-only precedent
workspaces. `README-ARXIV.md` gives reproduction from the public sources.

`evidence/` holds the generated check receipts, file identity records, complete
axiom output and frozen statement receipt. `relay/` holds the adapted scripts,
staging receipts, comparator sandbox invocations, runner/kernel logs, export
receipt and final process check. Vendor trees, .lake outputs, tar archives and
the Solution export stay in WSL. No lake command ran in the dev build folder.
All Python interpreters used isolated mode (-I), including the bubblewrap recorder.

## QB decisions

- R4 paper wording remains QB's: the public paper text still says the Z4 result
  is not formalized. This package does not modify the paper.
- Noise-diagram v1.3.0's `CITATION.cff` records DOI 10.5281/zenodo.24147268 while
  the package brief specifies 10.5281/zenodo.24178271. Both values are preserved
  in the receipts. QB should decide the public metadata correction. Source
  identity and verification pass independently of that discrepancy.

There is no mathematical or verification blocker. Theorem 12.11 on Z3,
Theorem 12.12's rate and all other excluded claims remain outside this package.
