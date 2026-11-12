# Statement read for the release package (session 3, 12 Nov 2026)

This file is the blind fidelity read of `ForgettingNaturalRule/Statements.lean`, copied byte for byte
below the line (source: `C:/Infanox/qb-relay-2026-10-22/blind-fidelity-fnr-2026-11-12/STATEMENT-READ.md`,
sha256 `9bb2d8cd5651b4b17e3e533cb533a1c7eb0e101964a224b15e8ec04532d9a2a4`). The reader read the session-2 DRAFT (sha256 `2d881dd35bff…`, unchanged from commit `6191506` to `92cff39`) and did not write it.

**Applied before the freeze, in commit `386de0d`** (the frozen file has sha256
`3e4f73e3bc4a71ac041e45186e4d992abcd294f33ad7cfe5f4c337b8c479b5d4`):
* **M-1, the one mismatch.** `TheoremA` is now the printed Theorem A, with no hypothesis:
  `def TheoremA : Prop := ErgodicityReduction`. The conditional form is kept as
  `def TheoremAFromDomino : Prop := DominoReduction → ErgodicityReduction`, exactly as the read proposed.
  `FNR.theorem_A : FNR.TheoremA` is proved in `Reduction.lean` (it is `FNR.ergodicity_reduction`), and
  `FNR.theorem_A_from_domino : FNR.TheoremAFromDomino` in `Main.lean`. No docstring calls the
  conditional form printed. The release package contains `Reduction.lean` and checks `FNR.theorem_A`,
  so the read's packaging consequence is met: Theorem A as printed is a release target.
* **Note 1, row S12.** Translation invariance over all of `ℤ⁶` is exact (the paper's Section 2.2
  convention). The docstring of `NaturalClassification` now cites that sentence and has no
  **[choice]** label; the proposition is unchanged. STATUS row S12 says "exact".
* Notes 2 and 3 (checker orientation, halting at time 0) are recorded in STATUS rows S6 and S13.
  Note 4 needs no change. Note 5 (paper wording) is for QB.

The comparator checks exactly these statements: the five holes of `Challenge.lean` are
`FNR.natural_classification : FNR.NaturalClassification`, `FNR.theorem_A : FNR.TheoremA`,
`FNR.machine_corollary : FNR.MachineCorollary`, `FNR.domino_reduction : FNR.DominoReduction` and
`FNR.domino_undecidable : FNR.DominoUndecidable`.

---

# Blind statement read: ForgettingNaturalRule/Statements.lean (DRAFT, session 2)

**Verdict: FIX REQUIRED** (one item, a designation fix with no new mathematics: `TheoremA` is
weaker than the printed Theorem A. Everything else is FAITHFUL.)

Reader: blind fidelity reader; did not write the file. `YOUR-TABLE.md` (same folder) was written
before STATUS.md was opened. No Lean process, no proof file, no forbidden file was opened.

## 1. Summary by proposition

| Proposition | Printed counterpart | Verdict |
|---|---|---|
| `NaturalClassification` | mainD = nw:classification minus nw:coalescence | EXACT (coalescence bound out by declared ruling; mainD itself does not contain it) |
| `HasTwoTIStationaryLaws` (UND) | "two distinct translation-invariant stationary laws" | EXACT (full ℤ⁶ invariance is the paper's own convention, Section 2.2) |
| `TilesPlane` | "R tiles the plane" (translations only) | EXACT (orientation = set:def-wang) |
| `Keeps` / `check` / `votes` / `natMap` / `natNbhd` / `natCA` | cardinal checker, boxes, h-of-q quorum, Γ × S, G_R | EXACT (all [choice]s harmless) |
| `epsStar` | `(2(18q)^2)^(-200)`, q = 5·16⁴ | EXACT |
| `UND.CA.IsErgodic` + `FNE.WeakTendsto` | unique invariant probability law + weak convergence from every initial law | EXACT |
| `ErgodicityReduction` | mainA | EXACT (extra true conjunct `IsPositiveRatePCA`, as nw:machine asserts) |
| **`TheoremA := DominoReduction → ErgodicityReduction`** | mainA (unconditional) | **MISMATCH: weaker than printed** |
| `DominoReduction` | first sentence of nw:machine; Berger/Robinson unseeded reduction | EXACT |
| `MachineCorollary` | nw:machine, all three sentences | EXACT / HARMLESS (sentence 3 read in its strongest form, M-indexed) |
| `IsPositiveRatePCA` | "positive-rate PCA" (02-setting) | HARMLESS (clauses (i)-(ii) automatically true for every UND.CA) |
| `DominoUndecidable`, `ErgodicityUndecidable`, `TheoremAUndecidable` | their docstrings | EXACT |

No clause is vacuous: the neighbourhood has 25·16⁴ points; the noise is uniform on all |R| + 1
letters; ε_* > 0; ergodicity requires a stationary probability law, uniqueness among all probability
laws, and convergence from every probability law; `TilesPlane` is false for ∅ and true for a tile
with N = S, E = W; `DominoReduction` is a true theorem, so `TheoremA` is not vacuous (only weaker).

## 2. The mismatch and the exact Lean change

**M-1. `TheoremA` carries a hypothesis that the printed Theorem A does not have.**
Printed (mainA): "There is a total computable map M ↦ W_M from Turing machines to finite Wang sets
such that, for every ε ∈ (0, ε_*], the positive-rate automaton obtained from G_{W_M} is ergodic if
and only if M halts." No hypothesis. The Berger-Robinson reduction is a cited step of the proof of
nw:machine ("Use the classical effective unseeded domino reduction..."), and the sentence after
mainA ("The only undecidability input in this route is...") describes the proof, not the
statement. `TheoremA := DominoReduction → ErgodicityReduction` is therefore strictly weaker than
mainA as a proposition. The exact printed statement is `ErgodicityReduction`, which STATUS.md says
is proved with no hypothesis (`FNR.ergodicity_reduction`, `Reduction.lean`).

Exact change in `ForgettingNaturalRule/Statements.lean`, replacing the current `TheoremA` block:

```lean
/-- **Theorem A on `ℤ⁶`** (introduction; Corollary `nw:machine`), as printed: no hypothesis. -/
def TheoremA : Prop := ErgodicityReduction

/-- Theorem A from its one classical input, the domino reduction of Berger and Robinson (the
route of the paper's proof of `nw:machine`). Weaker than `TheoremA`. -/
def TheoremAFromDomino : Prop := DominoReduction → ErgodicityReduction
```

with the matching changes outside the statement file: the current Main.lean theorem becomes
`theorem_A_from_domino : TheoremAFromDomino`, and `theorem_A : TheoremA` is
`ergodicity_reduction` (it lives where `Reduction.lean` is imported). Update
`scripts/audit_gen.py`/`Audit.lean` and STATUS rows S16 and the final-targets table to match.

Equivalent alternative if the definitions must not move: keep both definitions, but change the
`TheoremA` docstring from "**Theorem A on ℤ⁶** ..." to "Theorem A conditional on the domino
reduction (weaker than printed)", and make `FNR.ergodicity_reduction : FNR.ErgodicityReduction` the
target the release calls "Theorem A".

**Packaging consequence.** If QB's release package leaves out `Reduction.lean` (STATUS open item 2),
the package does not contain Theorem A as printed, only `TheoremAFromDomino`, and the claim
"Both printed theorems are proved exactly as printed" (STATUS line 12) must not appear for that
package. With `Reduction.lean` in, the claim is correct via `ergodicity_reduction`.

## 3. Non-blocking notes

1. **S12 is EXACT, not a [choice].** Section 2.2 of the paper says: "Spatial translation invariance
   always means invariance under every translation of ℤ⁶, unless a smaller group is explicitly
   named." So "spatially translation-invariant" in nw:classification already means all of ℤ⁶.
   Suggested docstring change in `NaturalClassification`: cite that sentence and drop the
   **[choice]** label. No change to the proposition.
2. **Checker orientation.** `Keeps` uses east = +e₁ (`c.E = b.W`), west = −e₁ (`b.E = c.W`),
   north = +e₂ (`c.N = b.S`), south = −e₂ (`b.N = c.S`), the same as `TilesPlane` and the paper's
   set:def-wang. STATUS S6 does not record this; worth one phrase.
3. **Halting at time 0.** `FNE.TuringMachine.Halts` counts a machine whose initial state 0 is halting
   as halting (n = 0); the paper says "enters a halting state". This affects only trivially
   decidable instances and is inherited from the frozen forgetting core. Harmless.
4. **`IsPositiveRatePCA` carries no information beyond the construction** (STATUS D10: proved for
   every UND.CA at 0 < ε ≤ 1). That mirrors the paper ("The process is therefore a probabilistic
   cellular automaton with positive rates"). Harmless.
5. **Paper-side staleness (not a Lean change).** The draft says "The natural theorem is not
   formalized" (after mainA), "The reduction above is not covered by the Lean development" (after
   nw:machine) and "Lean coverage remains exactly the old ℤ⁸ form" (Changes paragraph). Once this
   core is frozen, these sentences must be revised, and the revision must name which Lean target is
   Theorem A (see M-1).

## 4. Comparison with STATUS.md "Statement fidelity" (S1-S19) and Decisions (D1-D13)

| Row | STATUS | This read | Agreement |
|---|---|---|---|
| S1 | colours ℕ | HARMLESS | agree |
| S2 | TilesPlane, translations only | EXACT | agree |
| S3 | planar coordinates first | HARMLESS | agree |
| S4 | boxes via `Provider`, `offset` | EXACT (offset injective, checked) | agree |
| S5 | `Option R`, `letterEquiv` | EXACT / HARMLESS | agree |
| S6 | cardinal checker | EXACT | agree (note 2: record orientation) |
| S7 | quorum, `Classical.choose` | EXACT | agree |
| S8 | `natCA`, Γ × S, ⊥ extension | EXACT | agree |
| S9 | noise, process, ergodicity reused | EXACT | agree |
| S10 | `epsStar` | EXACT | agree |
| S11 | Theorem D | EXACT | agree |
| S12 | full ℤ⁶ invariance, listed as a choice ("nw:classification says spatially") | EXACT by the paper's Section 2.2 convention | **minor disagreement** (classification only; note 1) |
| S13 | FNE machine model | HARMLESS | agree (note 3 added) |
| S14 | `DominoReduction` = nw:machine sentence 1, Berger-Robinson | EXACT | agree |
| S15 | `IsPositiveRatePCA` four clauses | HARMLESS | agree |
| S16 | "`TheoremA := DominoReduction → ErgodicityReduction`" called the "printed reduction form" | `ErgodicityReduction` is the printed form; `TheoremA` (conditional) is weaker | **DISAGREE: M-1** |
| S17 | `MachineCorollary`, M-indexed undecidability | HARMLESS (strongest natural reading) | agree |
| S18 | `DominoUndecidable` | EXACT | agree |
| S19 | `TheoremAUndecidable` as a labelled corollary | EXACT to its docstring | agree |
| Final targets, line 12 vs line 32 | "Both printed theorems are proved exactly as printed" while `FNR.theorem_A` has hypothesis `DominoReduction` | True only through `FNR.ergodicity_reduction` (line 35) | **disagree on designation** (M-1) |
| D7 / QB ruling 1a | "Theorem A is now the printed reduction form, with the domino reduction as the named hypothesis" | The printed form has no hypothesis | **disagree** (M-1) |
| D4, D8-D12 | rule re-defined for proofs; machine model; TI clause; PCA; averaging layer; Reduction isolated | no statement-level issue; D12 is the source of M-1 (Main.lean cannot reach the unconditional form) | agree, with M-1 consequence |
| D1-D3, D5, D6, D13 | infrastructure / route | no fidelity content | n/a |

Items in my table not recorded in STATUS (no disagreement, just more explicit): the quantifier
order ∃W ∀ε ∀M (STATUS S16 has it); `offset` injectivity, so provider counts equal `|{a ∈ S : …}|`;
"blank readings do not vote"; the paper-side staleness of note 5.
