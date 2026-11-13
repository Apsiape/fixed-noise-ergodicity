# Release package complete — 12 Nov 2026

All requested release checks PASS: fresh no-resume serial replay (133
modules), reachable-constant precheck (116 constants), actual sandboxed
lake comparator with default kernel, Solution export, leanchecker --from-export,
nanoda with the standard three axioms, Classical.choice negative control (rejected
for the missing axiom), fresh complete axiom audit, source census/lint and pinned
dependency identity. See REPORT.md, SCOPE.md, README-ARXIV.md and evidence/.

Proof source is 321e81225e73db9311a6c871057b513bfa020a9f; the package is this
release commit (git log -1). All 31 original Lean files are unchanged. Frozen
Statements.lean SHA256 is 58cb7388400f05f2986d2b2cc9154a99a554eed4b384f10c8809b706d3b244c4.
No new mathematics; no Z3 or rate claim; no named hypothesis for any target.

Fresh release workspace: /opt/forgetting-lower-arxiv-2026-11-12 (lean-comparator).
Four public trees are byte-identical file by file: natural-rule 93, machine-family
104, noise-diagram 166, hard-model 135 files. The natural-rule tree is also
identical to v2.0.0. All nine pinned dependency sources match the public manifest.
Vendor/, .lake/, archives and exports remain WSL; package/evidence/relay are local
git records. No Lean tool or owned monitor remains running, and no process was
killed. No pushes, publications, installs, network fetches, outside contact or
subagents. Every Python invocation used -I. Original build guards are unchanged.

No required verification step remains. QB items: R4 paper wording and the
noise-diagram CITATION DOI discrepancy recorded in REPORT.md. Do not edit the
paper or frozen statements, and do not start the separate Z3 stretch here.

Procedural record: initial sandboxed git status/log was denied Permission denied;
the authorized elevated retry succeeded. An initial awk process inspection had
a quoting error; corrected pgrep checks succeeded before compilation. An extra
final blank line introduced while copying the model resource guard was removed;
its exact original bytes and all guard logic are unchanged. The staged-review
helper initially used the Windows default decoder for a UTF-8 receipt; explicit
UTF-8 fixed its final summary. No Lean check failed. No denial remains unresolved. Public predecessor warnings were retained without source edits.

The prior proof-session record, including the Ground rules word for word,
is preserved below as history.

---

# Status: the natural raw-Wang rule on Z4 — mandatory targets proved

Session 5, 12 Nov 2026. Local repository C:/Infanox/forgetting-lower-lean,
never pushed. Session-4 base: 4c490f6. WSL distro lean-comparator, workspace
/opt/forgetting-lower-lean/project. Lean 4.35.0; Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679. Namespace FLD, root ForgettingLower.

## Outcome

All three FROZEN targets are proved with no named assumptions:

| Proof | Exact frozen type |
|---|---|
| FLD.z4_classification | FLD.Z4Classification |
| FLD.z4_machine_corollary | FLD.Z4MachineCorollary |
| FLD.z4_raw_undecidable | FLD.Z4RawUndecidable |

The classification includes the common neighbourhood, ergodicity iff non-tiling,
two distinct invariant probability laws for tilers, all-time finite-window
all-start CFTP for non-tilers, and attraction from every initial probability law.
The machine corollary uses the same unconditional FNR domino family at every
allowed rate, including the positive-rate clause. The raw-family corollary is
the exact separate R1 target. The RELAY stopping condition is met.

No Z3 work or Kari hypothesis. No comparator, proof export, independent kernel
replay, packaged release or paper update is claimed.

## Statement of record: FROZEN

`ForgettingLower/Statements.lean` SHA256:
`58cb7388400f05f2986d2b2cc9154a99a554eed4b384f10c8809b706d3b244c4`.
This file was not edited and never changes again. QB's blind fidelity report
found FAITHFUL, no mismatches. Session 3 applied R1/R2/R3 before the freeze:

* R1: exact `Z4RawUndecidable` text added. The checked
  `FLD.raw_undecidable_of_machine_corollary` is only the implication
  `Z4MachineCorollary -> Z4RawUndecidable`; neither target is closed.
* R2: both Draft stubs removed; only target propositions are in Statements.
* R3: ten `[choice]` tags added; other pre-existing declaration tokens preserved.
* R4 remains QB's: no paper wording changes before core closure and packaging.

`Z4MachineCorollary` is STRONGER than the printed proof's last sentence:
every allowed rate, the machine-indexed family and the positive-rate clause.
It implies the printed sentence; R1 separately states the raw-family sentence.
`AllTimeCFTP`'s added forall t is an equivalent addition beyond the printed
words, by countability of times and finite windows. It is not merely making
the printed simultaneity explicit. Freeze receipt: evidence/SESSION-3-FREEZE.json.

## Session 5 proof closure

Forty new finished theorems in seven new modules and the final assemblies:

* Coherence/Tiling closes X: ul_down preserves a central label, ul_reach reaches
  every planar site, and ul_common pushes readings to a common earlier time.
  Separate east_edge/north_edge supply compatibility. tiles_of_UL constructs
  a full tiling directly; live_marked and extraction_ae give Lemma 12.8.
* Forget/Unique closes U: every genuine common-noise discrepancy is unflagged,
  live in one history and marked on the density event. disc_parent follows an
  actual dependency, giving an infinite ordinary marked path. raw_paths excludes
  it simultaneously for all roots. unique_complete_all gives agreement at ALL
  integer times, for every pair of complete histories, on one full-measure event.
* Forget/CFTP closes P: the generic UND compactness and attraction theorems are
  applied with their actual types. Deterministic timeNoise/complete_timeNoise and
  flow_timeNoise transfer the pullback theorem to every observation time on the
  SAME event, giving exactly AllTimeCFTP. No stochastic time-shift assumption or
  uniform lattice cutoff is introduced. IsErgodic includes all-law attraction.
* Memory/Cover closes M0: clone errors and blank liveness are in markedFrom at
  every finite time, hence in marked, using the actual three-box K+1 count.
* Forget/Roots closes M1 independently of the density event. A complete finite
  physical contour supplies distinct flags and a deterministic connected-set
  encoding in the degree-18q graph. For every cost >=12, root_measure_le proves
  P(marked root) <= 4 sum_{j>=0}(B^cost e)^(j+1). At cost=16860, exact e0 gives
  B^cost e <=1/32, hence root_bound <=1/4. Only fixed flag sets use independence.
* Memory/Branch and Memory/Invariant close M2: the clone/blank one-site bounds
  give memory gap >=1/2 and non-ergodicity; generic FNR.Avg.exists_stationary_le
  preserves the bounds in two stationary probability laws. The blank cylinder
  distinguishes them. No spatial invariance condition is added.
* Main and Reduction assemble z4_classification and both corollaries.

Sessions 1-4's density, contour, geometry, rule and coherence sources are unchanged.
All final results have only the standard axioms propext, Classical.choice,
Quot.sound; none depends on a named mathematical assumption or a proof hole.

## Proof-route differences

1. Extraction uses coherent labels directly, adapting FNR's checked route,
   rather than compactness of increasingly large patches. Separate planar edge
   matching remains essential and is used explicitly.
2. Sparse roots are proved in the sufficient weak form <=1/4, with the memory
   gap >=1/2. The printed intermediate <2e and gap 1-4e are not claimed.
   The frozen classification asserts two distinct invariant laws and is proved
   exactly; it has no quantitative memory bound.
3. All-time CFTP is obtained deterministically from all-time uniqueness by
   translating complete histories, with all times/windows already inside one
   probability-one event. A countable-intersection argument is unnecessary.
4. The invariant laws are temporal Cesaro limits. No spatial averaging or
   translation-invariance claim is needed for the frozen Z4 statement.

## Verification

Receipts: session-5-logs/, AXIOMS.txt, evidence/SESSION-5-TYPES.lean,
SESSION-5-ROOTS.txt and SESSION-5-CHECKS.json.

* Full guarded build PASS; explicit types of all 40 new theorems and example
  assignments to each exact frozen target PASS; zero warnings.
* Census 0 in 31 own Lean files; forbidden constructs none; lint PASS.
* Strict audit: 206 finished theorems (40 new); prefix audit 452 declarations,
  0 disallowed, 0 depending on sorryAx.
* Frozen statement SHA256 unchanged on Windows and WSL. Copied scripts unchanged.
* Every compiler used the unchanged serial/memory driver, lean -j1 -M5000,
  LEAN_NUM_THREADS=1, lock and >=8 GiB checks. No lake invocation.
* All Windows Python calls used python -I. No installs, network fetches,
  subagents, pushes, public actions, outside contact or precedent writes.
* Final process receipt records no Lean/lake process left on Windows or WSL.

## Next handoff

The requested Z4 proof work is complete. A later independent review/package
session can replay and export the exact three target proofs under the same
guards. QB's R4 paper updates still wait for packaging and are not ours to edit.
Z3 remains a separate stretch; it was not started.
