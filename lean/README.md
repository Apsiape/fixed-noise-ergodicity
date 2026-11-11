# Lean formalization: Theorem A on ℤ⁸

This directory proves Corollary 9.21 of the paper, Theorem A on ℤ⁸, and the undecidability of ergodicity in the family, in Lean 4 with Mathlib. The proof has no unproved step and no hypotheses, and it uses no axioms beyond Lean's three standard axioms `propext`, `Classical.choice` and `Quot.sound`. Appendix C of the paper describes the formalization.

## What is proved

`FixedNoiseErgodicity/Statements.lean` defines, transparently and with no proofs of substance, every object that occurs in Corollary 9.21, and states the corollary as one proposition:

```lean
def CorEight : Prop :=
    ∃ Rfam : TuringMachine → List Tile, Computable Rfam ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ eps0 → ∀ M : TuringMachine,
        IsPositiveRatePCA 6 (Rfam M).toFinset ε ∧
          (IsErgodic 6 (Rfam M).toFinset ε ↔ M.Halts)
```

Here `eps0` is ε₀ = 490000^(−99). In words: there is a total computable map M ↦ R_M from Turing machines to finite Wang sets such that, for every real ε with 0 < ε ≤ ε₀ and every machine M, the noisy quorum rule F^[6]_{R_M} on ℤ² × ℤ⁶ = ℤ⁸ with uniform replacement at rate ε is a positive-rate probabilistic cellular automaton, and it is ergodic if and only if M halts. Every definition of the statement file carries a comment naming the definition of the paper that it mirrors.

The undecidability is stated in the vocabulary of the statement file and of Mathlib only:

```lean
theorem cor_eight_undecidable_statement :
    ∃ Rfam : TuringMachine → List Tile, Computable Rfam ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ eps0 →
        (∀ M : TuringMachine, IsPositiveRatePCA 6 (Rfam M).toFinset ε ∧
          (IsErgodic 6 (Rfam M).toFinset ε ↔ M.Halts)) ∧
        ¬ ComputablePred (fun M : TuringMachine => IsErgodic 6 (Rfam M).toFinset ε) ∧
        ¬ REPred (fun M : TuringMachine => ¬ IsErgodic 6 (Rfam M).toFinset ε)
```

that is, for every rate in (0, ε₀], ergodicity in the family is not a computable predicate of the machine, and non-ergodicity is not even recursively enumerable. It is derived from Mathlib's theorems that the halting problem is undecidable, through a compiler from Mathlib's partial recursive codes to the encoded machines, whose computability is proved.

| Printed result | Lean name | File (under `FixedNoiseErgodicity/`) |
|---|---|---|
| Corollary 9.21 (Theorem A on ℤ⁸) | `FNE.cor_eight : FNE.CorEight` | `Main.lean` |
| Corollary 9.21 with its undecidability | `FNE.cor_eight_undecidable_statement` | `Undecidable.lean` |
| Undecidability for the family R_M of Definition 6.17, encoded as below | `FNE.cor_eight_undecidable`, `FNE.nonergodic_not_re` | `Undecidable.lean` |
| Halting of encoded machines is not computable, non-halting not recursively enumerable | `FNE.halts_not_computable`, `FNE.not_halts_not_re` | `Undecidable.lean` |
| Theorem B (Theorems 3.1 and 4.2), for all j ≥ 1 and k ≥ max(2, 2j) | `FNE.theoremB` | `TheoremB.lean` |
| Theorem 9.1 (three tokens) and Theorem C for R_M | `FNE.Three.three_tokens`, `FNE.Three.theoremC_familyR` | `Three/Board.lean`, `Three/Assembly.lean` |
| Theorem A on ℤ⁸ for R_M | `FNE.Three.eight_familyR` | `Three/Assembly.lean` |
| Computability of M ↦ R_M | `FNE.Family.computable_familyR` | `Family/Computable.lean` |
| Proposition 6.18 (nonhalting members tile) | `FNE.Family.tiles_of_not_halts` | `Family/FamilyR.lean` |
| Lemma 9.12 (corner lemma), in the form 𝒦(0) = ∅ on V_6 and on every V_r with r ≥ 6 | `FNE.Three.corner_lemma`, `FNE.Three.corner_lemma_box`, `FNE.Three.corner_lemma_V16` | `Three/Corner.lean` |
| Corollary 9.13 | `FNE.Three.corner_plane`, `FNE.Three.corner_plane_V16` | `Three/Lists.lean` |
| Appendix B: M° halts if and only if M halts; its head stays on the cells ≥ 1 and moves right from cell 1 | `FNE.Family.oHalts_iff`, `FNE.Family.oRun_oneSided` | `Family/Machine.lean` |

`Audit.lean` prints the axioms of 437 named theorems, these among them, and `AXIOMS.txt` is its output.

**Not formalized:** Theorem C in the general form of Theorem 7.8, Theorem 8.2, the other corollaries of Section 8 (among them Corollaries 8.8, 8.12 and 8.17), and Corollary 3.12. The corner lemma is formalized in the form that Corollary 9.13 uses, 𝒦(0) = ∅; the printed claim that every list on V_16 is empty is not formalized. The bound T(M) ≤ 2n + 2 of Lemma B.1(d) is not formalized.

## Choices in the formal statement

The formal statement renders the printed one with the following choices; Appendix C of the paper explains them.

- The family is quantified existentially, as in Theorem A of the introduction. The development proves the classification and the undecidability also for an encoded realization of the family R_M of Definition 6.17 (`Family.familyR`).
- A Wang set is computed as a finite list of tiles whose colours are natural numbers; computability of M ↦ F^[6]_{R_M} is rendered as computability of M ↦ R_M, from which the local rule is an explicit finite construction.
- A Turing machine is a finite transition list and a list of halting states, over natural-number states and symbols; the initial state and the blank are 0, and a pair without an entry is a step that changes nothing. A machine halts if, started on a blank two-sided tape, it enters a halting state. For such a machine the finite state set and tape alphabet from which the construction builds M° and the payload of R_M are both the labels below `bnd M`, one plus the largest target-state or written-symbol label of the table (0 for an empty table); labels at or above it are never reached from the blank tape.
- "Positive-rate probabilistic cellular automaton" is rendered by four clauses: translation covariance on ℤ⁸, a finite neighbourhood, the one-step product law (1 − ε)δ_{F(x)(v)} + ε·uniform, and positivity of every symbol.
- The process is defined through a realisation of the noise. Ergodicity means exactly one invariant probability measure π, and convergence of the law of X_t to π from every initial probability measure, against every bounded continuous function on the product of discrete spaces.
- "Undecidable" is Mathlib's `¬ ComputablePred`, for each fixed real rate ε ∈ (0, ε₀], with machines coded by the `Primcodable` instance of the statement file; non-ergodicity is in addition not `REPred`. The compiler uses one universal code chosen classically from Mathlib's `ToPartrec.Code.exists_code`; it is a `noncomputable def` whose Mathlib `Computable` property is proved.
- ℤ⁸ is written ℤ² × ℤ⁶, the provider indices {0, …, 6} are an option type, the checker bit is a Boolean, and the noise of time t + 1 has index t.
- Patterns and fact fields are total maps read on their domains, walls, flows and bits are small finite types, colours are coded injectively by natural numbers, and several lemmas are proved in slightly stronger or reorganized forms than printed. Each such choice is marked `[choice]` in a comment at the place where it is made.

All 46 `[choice]` comments are listed, with file, line and text, in `evidence/CHOICES.json`.

## What was checked

- **Pins.** Lean 4.35.0 (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. Every pin is in `lean-toolchain`, `lake-manifest.json` and `pins/`.
- **Comparator.** `Challenge.lean` imports only Mathlib (seven modules) and no file of this development. It contains `FixedNoiseErgodicity/Statements.lean` verbatim, with one more Mathlib import (`Mathlib.Computability.RE`) and two `run_cmd` lines that set the module name under which the copied definitions are recorded, so that their internal names agree with those of the development. It then states `FNE.cor_eight : CorEight` and `FNE.cor_eight_undecidable_statement` with their proofs left as `sorry`. `Solution.lean` imports the proofs, and `comparator.json` names the two theorems and permits only the three standard axioms. The command `lake comparator --config comparator.json` was run on Linux inside a bubblewrap 0.9.0 sandbox: it made its own exports of both files, checked that the two proved theorems have exactly the statements of the challenge, with the same definitions, and use no other axiom, and replayed them in Lean's kernel. It exited 0 after 89.283 s. Record: `evidence/COMPARATOR.json`.
- **Two kernel checkers.** The export of the solution (298,405,463 bytes, SHA-256 `5354f2678439dd21dfd1ab9fe7f74993ed0fc449a2d1e0993c9f5cba973df5c1`) has the roots `FNE.cor_eight`, `FNE.cor_eight_undecidable_statement`, `FNE.cor_eight_undecidable`, `FNE.nonergodic_not_re` and `FNE.halts_not_computable`, and contains every declaration on which they depend, Mathlib's included. `leanchecker` of Lean 4.35.0 (exit 0, 61.244 s) and `nanoda` (exit 0, 40.83 s, set to reject any axiom other than the three standard ones) each re-checked every declaration of it. Records, with the export command and the binary digests: `evidence/KERNEL-REPLAY.json`, `evidence/BINARY-DIGESTS.json`.
- **Axioms.** `Audit.lean` prints the axioms of 437 named theorems and checks the axioms of all 4,609 declarations of the development, private and generated ones included. Only `propext`, `Classical.choice` and `Quot.sound` occur. `AXIOMS.txt` is the complete output of the recorded build; `evidence/AXIOM-AUDIT.json` is its machine-readable form.
- **No admissions.** Apart from the two open proofs of `Challenge.lean`, no proof uses `sorry`; no file declares an axiom or uses `native_decide`, `implemented_by` or `extern` (`evidence/SOURCE-AUDIT.json`, `evidence/LINT.json`, `scripts/lint.sh`). `FixedNoiseErgodicity/Hypotheses.lean`, the place reserved for theorems of other authors that Mathlib lacks, declares nothing.
- **Port.** The proofs were developed with Lean 4.30.0 and a Mathlib snapshot of May 2026, and ported to the pins above. The port changed proof text in 28 of the 1,084 theorem and lemma blocks, in 14 files, and one import in `Hypotheses.lean`; no statement of a theorem or lemma and no definition changed, and `Statements.lean` is byte for byte that of the development. Records: `evidence/PROOF-PRESERVATION.json`, `evidence/PORT.diff`, `evidence/FROZEN-STATEMENT.json`, `evidence/ORIGINAL-SOURCE.json`.
- **Dependencies.** All 10,268 dependency source files match `pins/DEPENDENCY-SOURCES.json`. Mathlib's 8,624 library sources agree byte for byte with the official commit; the only file of the official archive that differs is the cache tool's `Cache/Requests.lean`, outside the import closure of the proofs (`evidence/DEPENDENCY-CHECK.json`, `evidence/UPSTREAM-MATHLIB-SOURCE-CHECK.json`). The recorded build compiled all 66 modules of the development serially from source, with prebuilt Mathlib objects (`evidence/BUILD.json`); Mathlib was not rebuilt from source, and the two kernel checkers re-check every Mathlib declaration that the proofs use.

## Reproduce

You need the Lean 4.35.0 toolchain (`lean` and `lake`) first on `PATH`, Python 3.11 or later, Git, and at least 8 GiB of available memory: the build runner refuses to start a compiler below 8 GiB, and each Lean process runs with `-j1 -M6144`. The build runs on Windows x86-64 and Linux x86-64.

1. Get the dependency sources. Clone each package listed in `pins/DEPENDENCIES.json` from its `url` into a directory named by its `name`, and check out its `rev` with Git line-ending conversion disabled, for example

   ```
   git -c core.autocrlf=false clone https://github.com/leanprover-community/mathlib4.git mathlib
   git -c core.autocrlf=false -C mathlib checkout 56a005855ea17e0b0958f73ec801ae140b0a1679
   ```

   and likewise `plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries` and `Cli`.

2. From this directory, copy them into `vendor/`:

   ```
   python -I -B prepare_dependencies.py --source-dir DIRECTORY_OF_THE_CLONES
   ```

   The helper checks every file against `pins/DEPENDENCY-SOURCES.json` and runs no Git command. It substitutes `cache-tool/Requests.lean` for one file of Mathlib's cache tool, outside the import closure of the proofs, so that the Mathlib build cache works with path dependencies.

3. From this directory, fetch the Mathlib build cache and build:

   ```
   lake exe cache get
   lake build
   ```

   `lake build` runs `scripts/replay.py`, which compiles the 66 modules of the development and then `Challenge.lean`, `Solution.lean` and `Audit.lean`, one Lean process at a time, and writes the output of `Audit.lean` to `AXIOMS.txt`. Compare it with the shipped `AXIOMS.txt`. `bash scripts/lint.sh` repeats the source lint.

4. Comparator, on Linux with bubblewrap installed: from this directory, run `lake comparator --config comparator.json`. The comparator sandbox masks `/home`, `/root` and `/tmp`, so keep the checkout outside them.

5. Kernel replays: export the solution with the toolchain's `leanexport`, from this directory, with the target list recorded in `evidence/KERNEL-REPLAY.json` (`export.command`):

   ```
   lake env leanexport Solution -- Quot Quot.mk Quot.lift Quot.ind FNE.cor_eight ... > Solution.ndjson
   ```

   then run `leanchecker --silent --from-export Solution.ndjson`, and `nanoda` with the configuration recorded in `evidence/KERNEL-REPLAY.json` (`nanoda_config`).

## Files

- `FixedNoiseErgodicity.lean`, `FixedNoiseErgodicity/`: the 66 modules of the development. `Statements.lean` is the statement file, `Main.lean` proves `FNE.cor_eight`, `Undecidable.lean` the undecidability, `TheoremB.lean` Theorem B, `Compiler/` the compiler from partial recursive codes, `Three/` Section 9, `Family/` Section 6 and Appendix B, `Scaffold/` Section 5 and Appendix A, `Section2/` to `Section4/` Sections 2 to 4, `Hypotheses.lean` the (empty) list of external results.
- `Challenge.lean`, `Solution.lean`, `comparator.json`: the comparator check.
- `Audit.lean`, `AXIOMS.txt`: the axiom audit and its output.
- `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, `pins/`: the pins. `pins/DEPENDENCIES.json` lists the source of every dependency, and `pins/DEPENDENCY-SOURCES.json` the hash of each of its files.
- `prepare_dependencies.py`, `cache-tool/`: preparation of `vendor/`.
- `scripts/`: `replay.py` (the serial, memory-capped build that `lake build` runs, with `resource_guard.py` and the module list `modules.json`), `lint.sh`, `build.sh` and `env.sh`, and `corner/`, the untrusted programs that produced the corner-lemma certificate in `Three/CornerData.lean`, which the Lean kernel checks.
- `evidence/`: the records of the checks above.

## Edits after verification

- Five Lean files differ from the verified sources only inside comments, where references to internal working notes were removed: `Main.lean` (line 4), `Hypotheses.lean` (line 4), `Section2/Ergodic.lean` (line 4), `Three/Corner.lean` (line 13) and `Three/CornerCheck.lean` (lines 6 and 53), all under `FixedNoiseErgodicity/`. No line of Lean code changed. The hashes in `evidence/` refer to the verified sources.
- `scripts/replay.py` drops a memory check that was specific to the machine of the recorded run, and the docstring of `scripts/resource_guard.py` was corrected. `prepare_dependencies.py` and `pins/DEPENDENCIES.json` are written for this release.
- In `evidence/`, machine-specific paths were removed, commands are shown relative to the toolchain and project directories, and references to logs that are not included were dropped. The numbers are those of the recorded runs.
- Comments in the sources refer to the development's working records (`BLUEPRINT.md`, `STATUS.md`, `HANDOFF.md`) and to its work sessions. These records are not included; the fidelity choices that they collect are the `[choice]` comments of the sources, listed in `evidence/CHOICES.json`.

## License

Authored Lean sources and scripts: MIT or Apache 2.0, at your option. Documentation and recorded outputs: CC BY 4.0. `cache-tool/Requests.lean` is a modified file of Mathlib's cache tool and stays under Mathlib's Apache License 2.0 (`cache-tool/LICENSE`). See `../RIGHTS.md`, `../NOTICE` and the license files at the root of the repository. Third-party rights are unchanged.
