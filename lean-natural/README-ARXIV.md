# Forgetting under noise is undecidable, v2.0.0 (the natural Wang rule on ℤ⁶): Lean 4.35 arXiv verification package

Pins: Lean 4.35.0 / eb6cafb7290e8bd5f2937522d8d804f58f02bafc; Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679
(vendored as nine path packages under `vendor/`, not in git). `evidence/` (and the receipts under `relay/`) contain
the results; `SCOPE.md` says what is formalized, by printed number; `STATEMENT-READ.md` is the blind fidelity read of
the statement file, with a note on the fixes applied before the freeze.

`Challenge.lean` imports only Mathlib. It contains the whole of `FixedNoiseErgodicity/Statements.lean` except its
import lines, verbatim excerpts of `UndecidablePhaseDiagram/Statements.lean` (`UPD.Machine` with `HaltsOn`, and
`UPD.Universal`), the whole of `UncomputableNoiseDiagram/Statements.lean` except its two import lines, and the whole
of the frozen `ForgettingNaturalRule/Statements.lean` (sha256 `3e4f73e3…`) except its import line, followed by
exactly five intended holes, none with a hypothesis: `FNR.natural_classification : NaturalClassification`
(Theorem D), `FNR.theorem_A : TheoremA` (Theorem A as printed), `FNR.machine_corollary : MachineCorollary`
(Corollary 3.1), `FNR.domino_reduction : DominoReduction` and `FNR.domino_undecidable : DominoUndecidable`.
`Solution.lean` imports the proved results (`ForgettingNaturalRule.Main`, `ForgettingNaturalRule.Reduction`).
`comparator.json` permits only `propext`, `Classical.choice` and `Quot.sound`. `Audit.lean` prints and strictly
audits every root of `ForgettingNaturalRule/Audit.lean`, checks the axioms of every imported declaration of the
development and of the imported modules of the three reused cores (private and generated ones included), and checks
the types of the five release targets (and of the two conditional forms kept in the development).

Reused cores (sources compiled here; `evidence/VENDOR-CORES.json` checks each vendored tree file by file):

- `vendor/FixedNoiseErgodicity`: the forgetting core (the `ℤ⁸` core of this paper), the `lean/` folder of the public
  release v1.4.0, DOI 10.5281/zenodo.24126025 (https://github.com/Apsiape/fixed-noise-ergodicity/tree/v1.4.0/lean;
  commit `bdfca9b`, `lean/` tree `30bc2660…`), byte-identical, vendored whole: `ForgettingNaturalRule.Reduction`
  imports `FixedNoiseErgodicity.Undecidable`.
- `vendor/UndecidablePhaseDiagram`: the hard-model core, the `lean/` folder of the public release v1.2.0 of "An
  uncomputable phase diagram at positive temperature for one classical lattice model", DOI 10.5281/zenodo.24144192
  (https://github.com/Apsiape/undecidable-phase-diagram/tree/v1.2.0/lean; tag `v1.2.0`, `lean/` tree `7da72621…`),
  byte-identical.
- `vendor/UncomputableNoiseDiagram`: the noise-diagram core of "One noisy cellular automaton with an uncomputable
  noise diagram", its Lean release package of 12 Nov 2026 (the noise-diagram relay's workspace without its own
  `vendor/` and build outputs; Lean sources identical to commit `ec67163` of its Lean repository). It is public as the
  `lean/` folder of that paper's release v1.2.0 (DOI 10.5281/zenodo.24174445), whose Lean sources are byte-identical
  (committed LF line endings) to the vendored ones.

`scripts/replay.py` compiles exactly the modules of the cores that this package imports, into this package's
`.lake/build/lib/lean`; `UndecidablePhaseDiagram/Statements.lean` is compiled with
`-Dbackward.isDefEq.respectTransparency=false`, as in its own release.

## Reproduce on the recorded Windows/WSL machine

The native Linux workspace is `/opt/forgetting-natural-rule-arxiv-2026-11-12-public` in the `lean-comparator` WSL
distribution, staged by `relay/stage.sh` and `relay/install.sh` from the inputs that `relay/pack.py` (the source
archive of commit `386de0d` and the package files) and `relay/pack_public_cores.py` write. The latter reads the two
public release repositories and packs the `lean/` folder of each release commit from its git blobs (the releases set
`* -text`, so these are the published bytes); its receipt `relay/public-cores-receipt.json` checks every file
against the release's working tree, its `SHA256SUMS` and the digests recorded by the noise-diagram relay. The
toolchain, bubblewrap and the nine dependency packages are copied with `cp -a` from the forgetting relay
`/opt/forgetting-arxiv-2026-11-10`. Do not place the workspace under `/home`, `/root` or `/tmp`: the standard
comparator sandbox masks those directories. (Session 3 ran the same package with the forgetting and hard-model cores
vendored from their relay workspaces, in `/opt/forgetting-natural-rule-arxiv-2026-11-12`, kept as its record; its
results are in the git history at commit `dac2a90`.)

From public sources elsewhere: put the `lean/` folders of the two public releases at `vendor/FixedNoiseErgodicity`
and `vendor/UndecidablePhaseDiagram`, and the nine dependency packages at `vendor/<name>` as listed in
`vendor/FixedNoiseErgodicity/pins/DEPENDENCIES.json` (their sources are listed file by file, with sha256, in
`pins/DEPENDENCY-SOURCES.json`; that release's `prepare_dependencies.py --check-only --source-dir vendor` checks
them), with Mathlib's prebuilt objects; the noise-diagram core is the `lean/` folder of its release v1.2.0 (DOI 10.5281/zenodo.24174445).

From Windows, start `host-memory-monitor.py` (workspace root; `relay/` in git) with `python -I -B` in a separate
process; it writes the live host-memory heartbeat `project/.host-memory.json` every 2 s and stops by itself on
`project/.host-memory.stop` or after its time limit. Every compiler, comparator, export and kernel run refuses to
start without a fresh heartbeat or below 8 GiB available (host and Linux); all compiles use `-j1 -M5000`, a 1800 s
timeout and a process-tree RSS watchdog (stop at 9.0 GB); one process at a time.

Within WSL, `cd /opt/forgetting-natural-rule-arxiv-2026-11-12-public/project`:

- Build from source (the needed core modules, the 16 modules of the development, `Challenge`, `Solution`,
  `Audit`): `python3 -I -B scripts/replay.py` (`--resume` skips modules whose source, imports and options are
  unchanged). The output of `Audit.lean` is written to `AXIOMS.txt`.
- Lint and census: `bash scripts/lint.sh`, `python3 -I -B scripts/sorry_census.py`.
- The sandboxed comparator with receipts: `python3 -I -B ../run-linux.py comparator` (exactly
  `lake comparator --config comparator.json`, with `COMPARATOR_BWRAP` pointing to the invocation recorder
  `../bwrap-record`; default sandbox and kernel; no supplied exports).
- The replay export: `python3 -I -B ../run-linux.py export` (leanexport of `Solution` for the five targets).
- The two kernel replays and the negative control: `python3 -I -B ../run-linux.py leanchecker`,
  `python3 -I -B ../run-linux.py nanoda`, `python3 -I -B ../run-linux.py nanoda-negative`.
- Generators and evidence: `python3 -I -B scripts/make_challenge.py --package .` (Challenge.lean and
  `../evidence/FROZEN-STATEMENT.json`), `python3 -I -B ../make_audit.py`, `python3 -I -B ../make_evidence.py`.

Mathlib was not rebuilt from source: the dependency sources match the pinned manifest of the public forgetting
release (`vendor/FixedNoiseErgodicity/pins/DEPENDENCY-SOURCES.json`) file by file (`evidence/DEPENDENCY-CHECK.json`),
and both standalone kernels replay the exported proof closure. The
development's working records (`STATUS.md`, `BLUEPRINT.md`; the session handoff note is not shipped) and its development scripts
(`scripts/build.py`, `env.sh`, `wsl.ps1`, `audit.sh`, `challenge_precheck.ps1`) are kept as they were at the source
commit; the development build used prebuilt core objects on `LEAN_PATH`, which this package does not.
