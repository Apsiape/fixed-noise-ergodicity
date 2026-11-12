# Blueprint: Lean core of the natural Wang rule ("Forgetting under noise is undecidable", v2.0.0)

Paper: S. Douglas and N. Mghirbi, "Forgetting under noise is undecidable", version 2.0.0 (draft,
12 Nov 2026). Sources (read only): the writer's draft
`C:/Infanox/qb-relay-2026-10-22/codesk-write-forgetting-v2-2026-11-12/paper/` and the readback's
`C:/Infanox/qb-relay-2026-10-22/opus-readback-forgetting-v2-2026-11-12/paper-fixed/` (preferred;
Section 2 `sec:natural`, Theorem D in the introduction, Theorem 2.1 `nw:classification` and
Corollary 3.1 `nw:machine` are byte-identical in both; the readback's verdict on the headline
statement is PASS). Authority on wording: `opus-verify-wang-transfer-2026-11-12/VERIFY.md`.
Session 1, 12 Nov 2026.

**Core (QB rulings of sessions 1 and 2: "exactly as printed").** (1) Theorem D: for every finite
Wang set `R` and every `0 < ε ≤ ε_* = (2(18q)²)^{-200}`, `q = 5·16⁴`, the rule `G_R` on `ℤ⁶` with
uniform whole-symbol replacement is ergodic iff `R` does not tile `ℤ²`; if `R` tiles, there are
two distinct translation-invariant stationary laws. (2) Theorem A on `ℤ⁶`, as printed, without
hypothesis: a total computable map `M ↦ W_M` such that, for every `ε ∈ (0, ε_*]`, the positive-rate
automaton obtained from `G_{W_M}` is ergodic iff `M` halts (session 3, after the blind fidelity
read; the classical domino reduction of Berger and Robinson, the input of the paper's proof, is
proved in `Reduction.lean`). The coalescence bound and nilpotency are outside the core (QB ruling 2
of session 2).

**Status in session 3: both printed theorems are closed, without hypothesis; the statement file is
FROZEN** (sha256 `3e4f73e3…`, `STATUS.md`). `FNR.natural_classification : FNR.NaturalClassification`
(`Main.lean`) and `FNR.theorem_A : FNR.TheoremA` (`Reduction.lean`) are proved, with Corollary
`nw:machine` (`FNR.machine_corollary`), the domino reduction (`FNR.domino_reduction`, from the
forgetting core's Theorem C) and Berger's theorem (`FNR.domino_undecidable`), all without
hypothesis, and the conditional forms `FNR.theorem_A_from_domino`, `FNR.theorem_A_undecidable`;
sorry census 0, every target depending only on `propext`, `Classical.choice`, `Quot.sound`
(`AXIOMS.txt`).

Conventions. Kind: **REUSE** (an audited declaration of a precedent core used as is through the
import), **ADAPT** (a precedent proof is the template; re-instantiated for raw tiles and cardinal
checks, with provenance), **NEW**. Status: STMT (statement file), DONE (proved, strict audit).
Precedent cores (read only): the noise-diagram core `UND` (`C:/Infanox/uncomputable-noise-diagram-lean`,
dev build `/opt/uncomputable-noise-diagram-lean/project`), the forgetting core `FNE` and the
hard-model core `UPD` (through `UND`).

---

## Part A. The proof route

The paper gives two routes for the non-tiling direction. The core uses the **qualitative
complete-history route** (paper, Section 2, "Complete histories: the qualitative route"), which
needs no forbidden square, no finite-age delay and no quantitative tail:

```
 Theorem A ◄── Theorem D ◄───────────────┬─ forgetting branch (¬ tiles ⇒ ergodic)
   ▲ domino reduction (hypothesis;        │    unique complete histories a.s. ─► UND Lemma 8.5 (REUSE)
   │  proved from FNE Theorem C, A4)      │
                                          │      ├─ a discrepancy is marked and has a discrepant parent
                                          │      │    ├─ complete coherence ⇒ an unmarked live reading gives a tiling
                                          │      │    │     └─ Lemmas nw:budget, nw:same, nw:neighbours (finite age)
                                          │      │    └─ locality of G_R
                                          │      └─ no infinite marked path a.s. (Lemma nw:paths at ε_*)
                                          │           └─ UND contours/packing/counting (REUSE), K_c ε ≤ 1/8
                                          └─ memory branch (tiles ⇒ not ergodic)
                                               ├─ two-cluster cover (Lemma nw:memorycover)
                                               ├─ sparse roots, weak form (P(v ∈ 𝓜) ≤ 1/4)
                                               ├─ UND memory ⇒ not ergodic (REUSE)
                                               └─ two translation-invariant stationary laws (M5):
                                                    temporal Cesàro limits with one-site bounds at
                                                    every site, then spatial averages along the six
                                                    coordinate directions (T1)
```

Consequently **Theorem 9.5 and Appendix A of the noise-diagram paper are not needed** (they serve
the quantitative bound `nw:coalescence`, which is outside the core), and neither are Lemmas
`nw:forbidden`, `nw:mortality`, `nw:allinput`, nor the coalescence estimate of `nw:ergodic`.

## Part B. Nodes

29 nodes: **3 pure REUSE**, **10 ADAPT** (a flagship proof re-instantiated), **16 NEW** (session 1:
24 nodes; session 2: T1, M5, A0, A3, A4). Every node is DONE. Lines are of this repository.

### B.0 Statements (`Statements.lean`, 319 lines, FROZEN in session 3, sha256 `3e4f73e3…`)

| node | Lean | kind | status |
|---|---|---|---|
| S0 tiles, sites `(u, P)`, the five boxes, `A_R = R ⊔ {⊥}`, the cardinal checker, the quorum, `G_R` as a `UND.CA 6`, `ε_*`, Theorem D (both sentences), positive-rate PCA, the domino reduction, Theorem A (as printed, no hypothesis), Theorem A from the domino reduction, Berger's theorem and the undecidability form, Corollary `nw:machine` | `FNR.TilesPlane`, `site`, `corner`, `Provider`, `offset`, `Letter`, `Keeps`, `check`, `votes`, `quorum`, `natMap`, `cardinal`, `natNbhd`, `letterEquiv`, `natCA`, `epsStar`, **`NaturalClassification`**, `siteLaw`, `IsPositiveRatePCA`, **`DominoReduction`**, `ErgodicityReduction`, **`TheoremA`**, `TheoremAFromDomino`, `DominoUndecidable`, `ErgodicityUndecidable`, `TheoremAUndecidable`, `MachineCorollary` | NEW; REUSE statement-level `FNE.Tile`, `FNE.WangSet`, `FNE.Plane`, `FNE.TuringMachine`, `FNE.TuringMachine.Halts`, `UND.Site`, `UND.CA` (with `apply`, `uniformLaw`, `noiseLaw`, `update`, `run`, `law`, `IsStationary`, `IsErgodic`, `shift`, `IsTranslationInvariant`, `HasTwoTIStationaryLaws`), `FNE.flagLaw`, `FNE.WeakTendsto` | STMT (FROZEN) |

### B.1 Constants (`Constants.lean`)

| node | Lean | kind | uses | status |
|---|---|---|---|---|
| A3 `Δ = 18q`, `B = 2Δ² = 16200·2³²`, `K_c = 4B^{101}`, `ε_* = B^{-200}`, `4(2Δ²)^{101g} ≤ K_c^g`, `K_c ε ≤ 4B^{-99} ≤ 1/8` | `FNR.Const.Delta`, `B`, `Kc`, `B_eq`, `epsStar_eq`, `epsStar_pos`, `epsStar_le_one`, `four_le_Kc_pow`, **`Kc_mul_le`** | NEW | `UND.Param.q` | DONE |

### B.2 The rule (`Rule/Local.lean`, `Rule/Bridge.lean`)

| node | Lean | kind | uses | status |
|---|---|---|---|---|
| R1 cardinal checker on `ℤ² × ℤ⁴` | `FNR.Rule.KeepsI`, `chkI`, `chkI_eq_some`, `chkI_congr`, `cardinal_sub_box` | ADAPT `UND.Rule.Keeps`, `chk` (Moore blocks → cardinal raw tiles) | — | DONE |
| R2 quorum `h` of `q`; uniqueness (`2h > q`); `≤ K` failed providers | `votesI`, **`GI`**, `quorum_unique`, `GI_eq_some_iff`, `card_failed_le` | ADAPT `UND.Rule.FR`, `quorum_unique`, `FR_eq_some_iff`, `UND.Coh.card_failed_le`; REUSE `UND.Rule.Prov`, `provOff`, `card_Prov` | R1 | DONE |
| R3 locality; a discrepancy has a discrepant parent in `Γ × S` | `GI_congr`, **`disc_parent`** | NEW | R2 | DONE |
| R4 the two references; cluster count | `Legal`, `clone`, `chkI_clone_inputs`, `GI_live_centres`, `card_bad_of_ne_clone`, **`twoCl_of_card`** | NEW (count after `UND.Coh.one_cluster`; REUSE `UND.Coh.card_cluster`, `TwoCl`, `MarkedAt`) | R1, R2 | DONE |
| S1 `natCA R` is `GI` | `siteEquiv_site`, `offset_eq`, `natMap_translate`, `natMap_eq`, `natMap_local`, **`natCA_apply`** | ADAPT `UND.Rule.caOf_apply`; REUSE `UND.Rule.siteEquiv` | R2, S0 | DONE |
| S2 decoding; one noisy update decoded | `dec`, **`dec_update`**, `dec_inj` | ADAPT `UND.Rule.update_decode` | S1 | DONE |
| S3 trajectories: complete ones from every time; the forward flow from time 0 | `IsTraj`, **`isTraj_of_complete`**, `complete_flag_eq`, `flowTraj`, **`isTraj_flow`** | ADAPT `UND.Coh.isFlagTraj_of_complete`; REUSE `UND.CA.IsComplete`, `flow`, `UND.Coh.flagsOf` | S2 | DONE |

### B.3 Coherence (`Coherence/Rel.lean`, `Coherence/Tiling.lean`)

| node | Lean | kind | uses | status |
|---|---|---|---|---|
| C1 Lemma `nw:budget` (`≤ K` providers with a marked Moore parent) | `UND.Coh.MClosed`, `MarkedAt`, `TwoCl`, `one_cluster`, `card_marked_le` | REUSE | — | DONE (UND) |
| C2 the injective unit-shift pairing, surplus `(75/16 - 4)K > 0`; transverse separation | `UND.Coh.PSrc`, `pHi`, `pLo`, `pHi_injective`, `pLo_injective`, `provOff_pair`, `exists_pair`, `sep`, `sep_zero`, `sep_step` | REUSE | — | DONE (UND) |
| C3 good providers | `FNR.Coh.UL`, `UL.gi`, `keepsI_live`, `ul_of_good`, `ul_nbr_of_good` | ADAPT `UND.Coh.UL`, `UL.drvA`, `ul_of_good` | R1, R2, S3 | DONE |
| C4 Lemmas `nw:same`, `nw:neighbours` (finite age) | **`coh_rel`** (`Rel` at `0, e₁, e₂`) | ADAPT `UND.Coh.coh_rel` (base case: same vertex for `0`; overlap `2h - q` and the east/north edge for `e₁, e₂`) | C1–C3 | DONE |
| C5 `V_t + Γ ⊂ V_{t-1}`; persistence; reach | **`coh_back`**, `ul_down`, `ul_move`, `ul_reach` | ADAPT `UND.Coh.coh_back`, `coh_persist`, `coh_cover` | C3 | DONE |
| C6 complete histories: an unmarked live reading gives a tiling; non-tiling ⇒ every live reading marked | `ul_common`, `ul_same`, `ul_east`, `ul_north`, **`tiles_of_UL`**, **`live_marked`** | ADAPT `UND.Coh.coherent_chart` | C4, C5 | DONE |

### B.4 The forgetting branch (`Forget/Paths.lean`, `Forget/Unique.lean`)

| node | Lean | kind | uses | status |
|---|---|---|---|---|
| P0 the marked field and its contours: `𝓜` (least closure), Lemma `nw:arms` (`f` distinct flags, `85e ≤ 4000(f-1)`, span), the packing of Lemma `nw:paths` (`N ≤ 50f`, `≤ 101f` edges), the encoding count (`nw:encoding`), `P(all flagged) = ε^f` | `UND.Coh.markedFrom`, `marked`, `marked_closed`, `flagsOf`; `UND.Contour.GroupedSystem.grouped_terminal_estimate` (through) `UND.Raw.exists_contour`; `UND.Raw.exists_cover`; `UND.Counting.card_encLe_le` (through) `UND.Raw.measure_le_tsum_from`; `UND.Raw.flags_measure`, `card_nbr_le` | REUSE | — | DONE (UND) |
| P1 Lemma `nw:paths` at `ε_*` (qualitative): no infinite marked path a.s., every root | `base_le`, `enc_le`, **`pathEv_null_nat`**, **`raw_paths_nat`** | ADAPT `UND.Raw.pathEv_null`, `raw_paths` (base `K_mem ε` → `K_c ε`, `c = 101`, degree `18q`) | P0, A3 | DONE |
| M3 Lemma `nw:sparse`, weak form: `P(v ∈ 𝓜) ≤ 1/4` | `tsum_pow_succ_le`, **`root_bound`** | NEW (the same union bound, `G = 1`) | P0, A3 | DONE |
| P2 a discrepancy of two complete histories is marked and propagates | **`disc_step`**, **`disc_path`** | NEW | C6, R3, S3 | DONE |
| P3 unique complete histories; ergodicity | **`unique_complete`**, **`ergodic_of_not_tiles`** | NEW wrapper; REUSE `UND.CA.ergodic_of_unique` (noise-diagram Lemma 8.5 with the PCA layer P1–P9) | P1, P2 | DONE |

### B.5 The memory branch (`Memory/Cover.lean`, `Memory/Branch.lean`)

| node | Lean | kind | uses | status |
|---|---|---|---|---|
| M2 Lemma `nw:memorycover` (clone errors and blank live letters lie in `𝓜^0 ⊂ 𝓜`) | `traj_succ`, **`clone_cover`**, **`blank_cover`**, `marked_of_markedFrom` | NEW | R4, S3, C1 | DONE |
| M4 Lemma `nw:memory` (gap `1/2` at every time) ⇒ not ergodic | `cloneCfg`, `blankCfg`, `dec_cloneCfg`, `dec_blankCfg`, `dec_siteEquiv`, `law_bad_le`, **`memory_branch`** | NEW; REUSE `UND.CA.law_dirac`, `noiseLaw₂_map_tau`, `flow_eq_run`, `measurable_run`, `measurableSet_cyl`, `isProbabilityMeasure_law`, `HasMemoryFrom`, `not_ergodic_of_memoryFrom` | M2, M3, S3 | DONE |

### B.5a The translation-invariant clause (`PCA/Average.lean`, `Memory/Invariant.lean`; session 2)

| node | Lean | kind | uses | status |
|---|---|---|---|---|
| T1 spatial averages of a stationary law along one direction: probability, weak subsequential limits, invariance along the direction (telescoping), kept stationarity, kept invariances, kept one-site bounds; invariance under unit translations ⇒ under `ℤ^d`; **a stationary law with one-site bounds at every site gives a translation-invariant one** (generic `UND.CA d`) | `FNR.Avg.shift_shift`, `map_shift_map_shift`, `map_shift_zero`, `isTI_of_unit`, `avg_le`, `avg_univ`, `savg`, `isProbabilityMeasure_savg`, `integral_savg`, `exists_savg_limit`, `abs_integral_savg_shift_le`, `isInv_of_savg_limit`, `savg_isInv`, `isInv_of_weakTendsto`, `isStationary_map_shift`, `isStationary_savg`, `isStationary_of_weakTendsto`, `measurableSet_site`, `savg_le`, `le_of_weakTendsto`, **`exists_TI`**, **`exists_stationary_le`** | NEW (pattern: `UND.CA.exists_cesaro_limit`, `isStationary_of_cesaro_limit`, `isTI_of_weakTendsto`); REUSE `UND.CA.law_map_shift`, `integral_law`, `PhiBCF`, `cylIndicator`, `integral_cylIndicator`, `cesaro`, `exists_cesaro_limit` | — | DONE |
| M5 Theorem D, last clause: memory bounds at every site; two distinct translation-invariant stationary laws | `clone_blank_le`, `blank_live_le`, **`twoTI_of_tiles`** | NEW | M2, M4 (`law_bad_le`), T1 | DONE |

### B.6 The printed theorems (`Main.lean`, `Reduction.lean`)

| node | Lean | kind | uses | status |
|---|---|---|---|---|
| A0 positive-rate PCA (any `UND.CA`, `0 < ε ≤ 1`) | `FNR.isPositiveRatePCA` | NEW; REUSE `UND.CA.apply_shift`, `apply_congr`, `law_dirac_one`, `siteLaw_pos` | — | DONE |
| A1 Theorem D | **`FNR.natural_classification`** | NEW | P3, M4, M5 | DONE |
| A2 Theorem A from the domino reduction (conditional form) | `theoremAFromDomino_of_classification`, **`FNR.theorem_A_from_domino`** | NEW | A0, A1 | DONE |
| A3 the undecidability form (corollary), from Berger's theorem | `theoremAUndecidable_of_classification`, **`FNR.theorem_A_undecidable`** | NEW (`Primrec.not`, `Computable.comp`) | A1 | DONE |
| A4 the domino reduction from the forgetting core's Theorem C; Berger's theorem; Theorem A, the undecidability form and Corollary `nw:machine` without hypothesis | `tilesPlane_iff`, `familyR_tiles_iff`, **`domino_reduction`**, **`ergodicity_reduction`**, **`theorem_A`** (Theorem A as printed), `domino_undecidable_of_reduction`, `ergodicityUndecidable_of_reduction`, **`domino_undecidable`**, **`ergodicity_undecidable`**, `machineCorollary_of_reduction`, **`machine_corollary`** | NEW; REUSE `FNE.Family.familyR`, `FNE.Family.computable_familyR`, `FNE.Family.tiles_of_not_halts`, `FNE.Three.eight_familyR`, `FNE.not_ergodic_of_tiles`, `FNE.halts_not_computable` | A0–A3 | DONE |

## Part C. Estimate in sessions (about one hour each)

| work | sessions | state |
|---|---|---|
| Set-up, blueprint, statement draft, skeleton | 1 (planned) | done in session 1 |
| The core nodes B.1–B.6 | planned 3–4 (calibrated on the flagship: its Lemmas 5.1–5.3, 8.5 and the PCA layer are reused, so about 1,600 new lines) | **done in session 1** (1,663 lines with the statement file, without `Audit.lean`) |
| The translation-invariant clause of Theorem D (now in the core, QB ruling 1b) | planned 1–1.5 | **done in session 2** (`PCA/Average.lean`, `Memory/Invariant.lean`, 457 lines; the averages taken in the exchanged order, F7) |
| Theorem A from the domino reduction (QB ruling 1a), Corollary `nw:machine`, the reduction proved | — | **done in session 2** |
| The blind read applied (Theorem A unconditional), statement frozen | — | **done in session 3** |
| Release package: Mathlib-only comparator challenge (transparent copies of the `FNE`, `UPD`, `UND` and `FNR` statement files or excerpts), vendored sources (23 `UND` modules; 4 `FNE` modules, or the whole forgetting core if `Reduction.lean` is included; the reachable `UPD` modules), two kernel replays (leanchecker, nanoda), statement eye-read | 1–2 | **done in session 3** (five hypothesis-free targets; 104 modules replayed, the whole forgetting core vendored; comparator, leanchecker, nanoda, axiom audit PASS) |
| Outside the core (QB ruling 2 of session 2): the coalescence bound `nw:coalescence` (Lemma `nw:forbidden` by compactness, finite-age mortality `nw:mortality`, the finite-`N` path tail, the all-input coefficient `q_t`) | 2–3 | not to be started |
| Outside the core: nilpotency `nw:nilpotent` (after `nw:mortality`) | 0.5 | not to be started |

Total for the core including its release package: **3–4 sessions** (2 spent).
