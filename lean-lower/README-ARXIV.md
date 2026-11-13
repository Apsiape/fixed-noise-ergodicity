# Z4 natural Wang rule: Lean 4.35 release package

This is the verification package for Theorem 12.5 and its machine and raw-family
undecidability corollaries. `SCOPE.md` defines the claim precisely. The frozen
statement file never changes; the proof source is commit
`321e81225e73db9311a6c871057b513bfa020a9f`. `REPORT.md`, `evidence/` and `relay/`
contain the results and reproduction receipts. Nothing was pushed or published.

`Challenge.lean` imports only Mathlib and has exactly three intended holes:
`FLD.z4_classification : FLD.Z4Classification`,
`FLD.z4_machine_corollary : FLD.Z4MachineCorollary`, and
`FLD.z4_raw_undecidable : FLD.Z4RawUndecidable`.
There are no named hypotheses. The generator copies the whole statement files of
the machine-family, noise-diagram, natural-rule and frozen Z4 cores except their
imports, plus the same hard-model excerpts as the natural-rule challenge. It
asserts all five statement hashes and re-extracts each copy. Module names and
per-file caches are handled exactly as in the model package. The reachable
statement constants are compared against the development before the comparator.

`Solution.lean` imports the completed proof modules. `comparator.json` permits
only `propext`, `Classical.choice`, and `Quot.sound`. `Audit.lean` strictly audits
all development roots, checks every imported declaration of this core and the
four precedent cores (private and generated declarations included), rejects
project axiom declarations and unexpected axioms, and checks all three exact types.

## Reproduction from public sources

Use Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, including the
same `lake`, `leanexport`, `leanchecker` and `nanoda_bin` tools whose digests are
in `evidence/BINARY-DIGESTS.json`. Mathlib is
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

Put these public release folders at the indicated locations:

- [Forgetting v2.1.0, lean-natural](https://github.com/Apsiape/fixed-noise-ergodicity/tree/v2.1.0/lean-natural)
  -> `vendor/ForgettingNaturalRule` (DOI 10.5281/zenodo.24178276).
- [Forgetting v2.1.0, lean](https://github.com/Apsiape/fixed-noise-ergodicity/tree/v2.1.0/lean)
  -> `vendor/FixedNoiseErgodicity` (same DOI).
- [Noise diagram v1.3.0, lean](https://github.com/Apsiape/uncomputable-noise-diagram/tree/v1.3.0/lean)
  -> `vendor/UncomputableNoiseDiagram` (DOI 10.5281/zenodo.24178271).
- [Hard model v1.2.0, lean](https://github.com/Apsiape/undecidable-phase-diagram/tree/v1.2.0/lean)
  -> `vendor/UndecidablePhaseDiagram` (DOI 10.5281/zenodo.24144192).

The natural-rule folder is identical to v2.0.0. The four recorded release commits,
tree hashes and every file digest are in `relay/public-cores-receipt.json`.
The noise-diagram release's CITATION.cff DOI differs from the requested v1.3.0 DOI;
the receipt records both values without changing the source release. This metadata
discrepancy does not affect the file identity checks or proof checks.

Put the nine packages `plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`,
`aesop`, `Qq`, `batteries`, `Cli`, and `mathlib` at `vendor/<name>`, at the revisions
listed in `vendor/FixedNoiseErgodicity/pins/DEPENDENCIES.json`, with their prebuilt
objects. The file-by-file source manifest is
`vendor/FixedNoiseErgodicity/pins/DEPENDENCY-SOURCES.json`.
`lake-manifest.json` uses local path packages, so no dependency fetch is needed.

The recorded Linux workspace is `/opt/forgetting-lower-arxiv-2026-11-12` in WSL
`lean-comparator`, with the source and package in `project/`, the pinned toolchain
in `toolchain/`, bubblewrap in `bubblewrap/`, and relay runners at the workspace
root. Do not put it under `/home`, `/root` or `/tmp`: the default comparator
sandbox masks those directories. `relay/pack.py`, `pack_public_cores.py`,
`stage.sh` and `install.sh` adapt the natural-rule package's staging procedure.
They read precedent workspaces and public releases without modifying them.

Start the Windows heartbeat using `python -I -B relay/host-memory-monitor.py`
(the recorded workspace is its default). It writes memory status every two
seconds and stops on `project/.host-memory.stop` or its six-hour timeout. Before
launching a run, verify no Lean tool is running anywhere on the machine. Every
compiler uses the copied guards: one process, `lean -j1 -M5000`,
`LEAN_NUM_THREADS=1`, a lock, at least 8 GiB available on both Windows and Linux,
a fresh heartbeat, 1800 seconds per module, and a 9.0 GB process-tree watchdog.
No guard is weakened. Do not use lake in the development workspace.

With the release root as the current directory, run these commands serially:

```sh
python3 -I -B project/scripts/make_challenge.py --package project
python3 -I -B make_audit.py
cd project
python3 -I -B scripts/replay.py
cd ..
python3 -I -B precheck.py
python3 -I -B run-linux.py comparator
python3 -I -B run-linux.py export
python3 -I -B run-linux.py leanchecker
python3 -I -B run-linux.py nanoda
python3 -I -B run-linux.py nanoda-negative
python3 -I -B make_evidence.py
```

The first replay is fresh, with no `--resume`. The comparator is an actual
`lake comparator --config comparator.json`, with bubblewrap and the default
kernel, no supplied export and no sandbox bypass. `bwrap-record` records the
invocations and enforces one thread; its Python interpreter uses `-I`.
The standalone export names all three targets. `leanchecker --from-export` and
`nanoda_bin` replay the same export; nanoda allows only the three standard axioms.
The negative control removes `Classical.choice` and must reject that export for
the missing permission. `make_evidence.py` requires every recorded check to pass.

`scripts/challenge_precheck.ps1` invokes the same guarded release pre-check from
Windows. Full logs remain in WSL. Lint and development census are
`bash scripts/lint.sh` and `python3 -I -B scripts/sorry_census.py` from `project/`.
The package source audit additionally verifies exactly three holes, all confined
to Challenge. The Solution's axiom audit has zero dependencies on proof holes.
Stop the heartbeat and verify no Lean tool remains running after verification.

`vendor/`, `.lake/`, tar archives and exports stay in WSL and are not committed.
Package files, source pins, receipts and relay records are committed locally.
