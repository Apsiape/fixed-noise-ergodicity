# Lean core: the natural rule on ℤ⁴

This package proves Theorem 12.5 of "Forgetting under noise is undecidable" and its two frozen ℤ⁴ undecidability corollaries. The statement source and all proof sources are unchanged. The three final results take no named hypotheses:

* `FLD.z4_classification : FLD.Z4Classification`
* `FLD.z4_machine_corollary : FLD.Z4MachineCorollary`
* `FLD.z4_raw_undecidable : FLD.Z4RawUndecidable`

## Reproduce

Install the toolchain specified by `lean-toolchain` (Lean 4.35.0), and have Git and Mathlib's cache prerequisites available. From this directory run:

```sh
export LEAN_NUM_THREADS=1
lake exe cache get
lake build
lake env lean -j1 -M5000 Audit.lean
```

The cache command fetches the pinned Git dependencies and Mathlib's standard build cache. Plain `lake build` compiles the complete 31-module `ForgettingLower` library and the 99 reused proof-core modules from the shipped sources. The audit prints the recorded roots and checks their axiom dependencies. Compare the axiom set per named root with `AXIOMS.txt`; the only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. The final theorems have no named assumptions. The standard build does not run the comparator, the custom Python replay, or independent kernel replays, and does not rewrite `AXIOMS.txt`.

Allow at least 8 GiB of available physical memory and run one Lean compiler process on the machine at a time. The root package passes `-j1 -M5000`; the unchanged standardized FixedNoiseErgodicity and UndecidablePhaseDiagram package caps are 6144 MiB, and the other cores use 5000 MiB. On PowerShell set `$env:LEAN_NUM_THREADS = '1'`. Compiler thread limits do not provide a machine-wide process lock: serialize launches externally and check memory before compiling. This toolchain's Lake has no `lake build -j1` option.

Mathlib is required by Git at `56a005855ea17e0b0958f73ec801ae140b0a1679`; the Lake-generated manifest pins its eight inherited dependencies to the recorded revisions. Use the shipped manifest; ordinary reproduction does not require `lake update`. The stock Mathlib cache tool is used unchanged.

`Challenge.lean`, `Solution.lean`, and `Audit.lean` are ordinary files checked with `lake env lean -j1 -M5000 FILE.lean`. Challenge retains its three intentional comparator holes and is excluded from the default library. Library and final audit output must have no `declaration uses sorry` warnings.

The reused cores are real local Lake packages in `deps/`, declared with `require <Core> from "deps/<Core>"`. Only the recorded import closure is shipped, byte for byte: FixedNoiseErgodicity (61 modules) and ForgettingNaturalRule (14) from Apsiape/fixed-noise-ergodicity at `9d6cc4d439d6ce6a7e88a6d603c86f0fea0b4fd8`, UncomputableNoiseDiagram (23) from Apsiape/uncomputable-noise-diagram at `v1.4.0`, and UndecidablePhaseDiagram (1) from Apsiape/undecidable-phase-diagram at `3f112474185fb14e02628e04ff7090e931d8661a`. One identical copy of each core and one Mathlib resolve. No cross-repository source path is required. `deps/** -text` preserves their original line endings when tracked by Git.

`UPDStatements` is a separate library whose only root is `UndecidablePhaseDiagram.Statements`. It supplies `-Dbackward.isDefEq.respectTransparency=false` for that unchanged module's Lean 4.35 `Fintype` derivations. Other modules retain their original elaboration options.

The Python replay, evidence, and previous instructions below are retained as optional historical tools. They assume the old `vendor/` layout, prebuilt objects, and a host-memory heartbeat; plain `lake build` does not invoke them. Run historical preparation in a separate copy and retain the standard manifest in this one. The earlier comparator and independent kernel results are recorded in `evidence/`, `REPORT.md`, and `README-ARXIV.md`; ordinary reproduction does not repeat those checks.

## Scope and records

`SCOPE.md` states exactly which printed sentences each declaration covers. Not formalized here: the ℤ³ family (Theorem 12.11), the exponential rates of version 2.1.0 (Theorem 12.12), the all-Gibbs Corollary 12.14 of version 2.2.0, and every result outside the three above. `ForgettingLower/Statements.lean` is the frozen statement file; it passed a blind fidelity read (`STATEMENT-READ.md`). `REPORT.md` records the package checks of commit a471ef3 (a fresh serial replay of 133 modules, a sandboxed comparator, leanchecker and nanoda with a negative control, and the axiom audit); `evidence/`, `session-5-logs/` and `AXIOMS.txt` hold the receipts. The conversion to the standard Lake layout changed only build configuration and documentation: every Lean proof and statement file is byte-identical to that commit.
