# Blueprint: Theorem 12.5 and the Z4 undecidability corollary

Session 5 completion, 12 Nov 2026. Statement FROZEN after QB rulings R1/R2/R3;
STATUS.md records its SHA256. Never edit Statements.lean again.
Read RELAY.md in full; its Ground rules are binding verbatim. No delegation used.
Historical estimates below are retained; mandatory Z4 closure was achieved in session 5.
Z3 is deferred until BOTH mandatory targets have zero-hole proofs.

## Statement and conventions

Namespace FLD; module root ForgettingLower. All definitions are transparent.
Statements.lean adapts FNR's frozen rule definition to Site 4 and Fin 2 transverse
coordinates, three boxes, K=256 and h=512. It reuses FNE.Tile/WangSet/Plane,
FNR.TilesPlane/Letter/letterEquiv/cardinal/IsPositiveRatePCA, and UND.CA with its
actual noise, laws, stationarity, ergodicity and weak convergence. No replacement
notion of ergodicity is introduced. No named hypothesis for a result of ours.

Z4Classification states every sentence of ld:z4. AllTimeCFTP explicitly places
all finite windows AND all integer observation times inside one almost-sure
quantifier. This is slightly more explicit than UND.PullbackEventuallySingleton;
it is obtainable by countable intersections and time shifts, not a new stochastic
assumption. HasTwoInvariantLaws asserts exactly two distinct invariant probability
laws; no translation-invariance demand is added. Empty R is included.
Z4MachineCorollary quantifies one computable W before the rate and includes the
same-W domino equivalence and no computable halting/ergodicity decider.

## Proof nodes, reuse and dependencies

| Node / planned module | Kind and exact precedent | Dependencies | Estimate |
|---|---|---|---|
| S (FROZEN): transparent definitions and target types, Statements | ADAPT FNR.Statements rule; REUSE FNR.TilesPlane, UND.CA.IsErgodic, UND.CA.flow/noiseLaw2 | none | session 1 |
| C: constants and alphabet/provider cardinalities, Constants | ADAPT FNR.Const; NEW density arithmetic | S | 0.5 |
| G (DONE): ordinary graph and finitary least marked closure, Geometry/Marked | ADAPT UND.Raw.par/nbr, UND.Coh.markedFrom/marked_closed; dimensions/clusters change, cannot reuse their concrete types | S,C | 0.5–1 |
| G1 (DONE): three balanced potentials and good/bad gains | ADAPT UND.Raw.psi/isPotential_psi: 3 charges, good 130, bad 350 | G,C | 0.5 |
| T (DONE, deterministic part): finite physical contours with distinct flags | REUSE generic UND.Contour.GroupedSystem.grouped_terminal_estimate, witness_connected, singleton_two_le, witness_span; ADAPT UND.Raw.exists_contour projection | G,G1 | 1–2 |
| T1 (DONE): exact earliest-terminal bracket for EVERY contour vertex | NEW checked sharpening/instantiation: Contour/Bracket proves every arm vertex reaches its actual terminal; Contour/Finite chooses the actual earliest flag | T | 0.5–1 |
| D0: greedy skip/slab selection on finite H-occurrence positions | NEW; selected parent depths strictly beyond previous full terminal slab; final contour is NEVER truncated | C (abstract combinatorial leaf independent of contour existence) | session 1 first proof priority |
| D1 (DONE): disjoint physical terminals and mass accounting | NEW: slabs disjoint, each f_j pays at most 12(f_j-1)+1 <=12 f_j positions; total cardinal exactly sum f_j | D0,T1 | 0.5 |
| D2 (DONE): whole connected union and n <= N+12f <=16860f | ADAPT UND.Raw.exists_cover, NEW whole-N-edge path accounting | D0,D1,T | 0.5 |
| D3 (DONE): event bound 4 sum_{f>=ceil(delta*N/12)} (B^16860*e)^f | REUSE FNE.EdgeCount connected-edge encodings (through UND.Contour.Counting); ADAPT FNR.Forget.enc_le / UND.Raw.flags_measure; fixed deterministic terminal sets only | D2,C | 0.5–1 |
| D4 (DONE): all-path density at every root and no infinite all-M paths | NEW summable-tail/Borel–Cantelli application; ADAPT UND.Raw.raw_paths measure layer | D3 | 0.5 |
| R (DONE): checker/quorum locality, unique live quorum, discrepancies | REUSE planar FNR.Rule.chkI_eq_some/chkI_congr where types match; ADAPT FNR.Rule.quorum_unique/GI_eq_some_iff/card_failed_le/disc_parent, Bridge.natCA_apply | S,C | 0.5–1 |
| Q (DONE): unmarked budget and clean successful providers | ADAPT UND.Coh budget and FNR local count, h-K=K | G,R,C | 0.5 |
| A (DONE): amortized same-site coherence, ld:z4coherence | NEW: 720 injective shifted pairs >512 failures only at non-H steps; arbitrary clean parents otherwise; positive span drift and two all-path density bounds | D4,Q,R | 1 |
| E (DONE): planar edge matching, ld:z4edges | NEW: clean checker star plus A at neighbouring planar site one time earlier; cannot infer edges from same-site agreement alone | A,Q,R | 0.5 |
| X (DONE): planar extraction, ld:z4extract | ADAPT FNR.Coh.ul_down/move/reach/common; direct coherent-label tiling with separate FLD east/north edges | A,E,Q | session 5 |
| U (DONE): unique complete histories at all times | ADAPT FNR.Forget.disc_step/disc_path; genuine FLD complete histories, FLD Density.raw_paths | X,D4,R | session 5 |
| P (DONE): all-time CFTP and all-law attraction | REUSE UND.CA compactness/ergodic_of_unique; NEW deterministic timeNoise/complete_timeNoise/flow_timeNoise repackaging | U | session 5 |
| M0 (DONE): tiling/blank error covers | ADAPT FNR.Memory.Cover with actual FLD K+1/two-cluster geometry and finite-past closure | Q,R,G | session 5 |
| M1 (DONE): sparse roots | NEW FLD physical contour encoding, generic cost>=12; REUSE UND.Counting, FLD flags_measure; cost16860 gives base<=1/32 and root<=1/4 | T,C | session 5 |
| M2 (DONE): two invariant probability laws | REUSE generic FNR.Avg.exists_stationary_le; ADAPT FNR.Memory.Branch/Invariant, no spatial averaging | M0,M1,R | session 5 |
| Z4 (DONE): every frozen ld:z4 clause | FLD.z4_classification : Z4Classification, no named assumptions | P,M2,R | session 5 |
| Z4 reduction and both corollaries (DONE) | REUSE unconditional FNR.domino_reduction/positive-rate theorem/FNE halting undecidability; exact FLD machine and raw targets | Z4,C | session 5 |
| Development validation (DONE); packaging deferred | Unchanged copied guards, exact target type assignments, census/lint/strict audit | all | session 5 |

Reuse candidates above are located in precedent sources; only the declarations
actually used in the checked files have had their application types checked here.
Every further use must be Lean type-checked. In particular UND concrete raw-path theorems use five clusters
and cannot be applied to the three-box graph by renaming.

## Density proof obligations that must stay visible

1. A contour at parent depth k+1 has every terminal and vertex between that depth
and its actual last depth. The next selected parent depth is STRICTLY greater
than the preceding last depth, including equality endpoints.
2. Greedy selection covers every H occurrence, including skipped ones. Its last
contour may extend below depth N; retain its whole flag set and edge set.
3. Flags from distinct slabs are disjoint physical vertices; count the cardinal
of their union as a sum, not a multiset of repeated flags.
4. The union contains the WHOLE length-N path, all spurs and full contours. Its
entropy is included via N <=16848 f and n <=16860 f.
5. Union-bound only over deterministic connected unions and f-element terminal
sets. Adaptive path/contour/slab selection supplies a witness; it does not supply
independence. Borel–Cantelli is over N at a fixed root, then countably many roots.
6. Root-dependent random N0 only; no uniform cutoff over the whole lattice.

## Historical session 1 checkpoint criteria (superseded by freeze)

Build the draft skeleton with all holes confined to Statements.lean, record the
census, prove D0/D1 arithmetic leaves first, keep STATUS/HANDOFF current, commit
locally with the exact identity specified in RELAY.md. QB performs the separate
blind statement read; no freeze is inferred from a successful build.

## Stretch (only after zero-hole mandatory targets)

Z3 generator, north/east determinism, exact z(i,t) geometry, same-index difference
transport, live-cone tiling compactness, moving tiling orbit and fixed LIVE event.
One named published Kari hypothesis may be introduced only then, exactly as the
Kari 1992 / Kari 2005 section 2.8 Theorem 5 statement in RELAY.md. No other results
of ours become assumptions.

## Completion markers through session 5

All mandatory nodes are DONE. S remains FROZEN, byte-unchanged. Sessions1-4's
contours, density, geometry, actual rule bridge, providers, same-site coherence
and separate edges remain intact. Session5 adds X/U/P/M0/M1/M2 and final assembly.

FLD.z4_classification : FLD.Z4Classification,
FLD.z4_machine_corollary : FLD.Z4MachineCorollary, and
FLD.z4_raw_undecidable : FLD.Z4RawUndecidable have no named hypotheses.
The machine corollary retains its stronger all-rate/same-family/positive-rate
content; the separate raw target is exactly R1. AllTimeCFTP's added forall t is
proved on the same event by deterministic time translation of complete histories.

The sparse-root proof is independent of all-path density: complete finite
contours with distinct physical flags and connected encodings give a generic
cost>=12 union bound. Cost16860 uses the existing exact-rate slack to get
root<=1/4, sufficient for memory gap>=1/2 and two distinct stationary laws.
The printed intermediate <2e is not claimed. Extraction uses direct coherent
labels and separate planar edges instead of patch compactness. Temporal Cesaro
limits suffice; no spatial invariance is added. See STATUS for route differences.

Session5:206 strictly audited theorems (40 new),31 own Lean files,prefix452,
disallowed0,sorry-dependent0. Full guarded build, exact types, census, lint and
audit PASS with zero warnings. No named assumptions, Z3 work, Kari hypothesis,
paper changes, comparator/export, independent kernel replay or packaged release.
The requested Z4 completion stopping condition is met; R4 paper updates remain QB's.
