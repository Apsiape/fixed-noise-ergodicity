# Statement read for the Z4 release package (12 Nov 2026)

The blind read below is copied verbatim from the lower-dimensions fidelity relay.
Source SHA256: `f40c09262f0acb31eb27bbc9180d2c11aeb6e09a0cc04af2f2c58b57b0fc698c`.
Rulings R1-R3 were applied before the freeze in commit eb00b98: the literal raw-family
undecidability proposition was added; both draft proof stubs were removed; ten
`[choice]` tags were added. The frozen SHA256 is `58cb7388400f05f2986d2b2cc9154a99a554eed4b384f10c8809b706d3b244c4`.
The three release targets have no named hypotheses. R4 (paper wording) remains QB's.

---

# Statement read: `ForgettingLower/Statements.lean` vs Theorem 12.5 (`ld:z4`)

**FAITHFUL**

Reader: Claude Opus 5.5, cross-family blind read (the file was written by a GPT-6.1 Sol agent).
File read: `C:/Infanox/forgetting-lower-lean/ForgettingLower/Statements.lean`, sha256
`a0e5c8e394570302950559108aa6d4159b1fbe2e5d6c03cc67b05dc7012f68ef` (the same hash STATUS.md records,
and the same as the WSL build copy). Paper: v2.0.0 `sections/12-lower-dimensions.tex`, sha256
`0e5090c43e3aa6607a561132437c870ff5ea08212030ae0c15c1791a47042b63`. The row-by-row table is in
`YOUR-TABLE.md` (written before STATUS.md, BLUEPRINT.md, HANDOFF.md, README.md and RELAY.md were opened).

## Mismatches

None. Every printed clause of Theorem 12.5 is rendered EXACT or with a HARMLESS DEVIATION:

- Quantifiers: `∀ R (e : ℝ), 0 < e → e ≤ eps0`. `eps0 = ((382205952 : ℝ) ^ 33720)⁻¹`, the printed
  value, and it is a closed term, so it is uniform in `R`.
- Alphabet: `Option R`, encoded as `Fin |A_R|` by a bijection.
- Boxes: `S₀ = {0..15}²`, `S₁ = 160e₁ + S₀`, `S₂ = 160e₂ + S₀`. They are pairwise disjoint, and the
  768 `Provider`s map injectively onto `S`.
- Quorum: `512 ≤ votes`.
- Neighbourhood: `Γ × S`, with no `R` in the definition.
- Checker: all five cardinal letters must be live, and the four centre-to-neighbour edges must
  match, oriented exactly as in `TilesPlane`.
- Noise: the frozen cores' uniform whole-symbol replacement after the rule.
- Ergodicity: `UND.CA.IsErgodic`, reused verbatim. It means a unique stationary probability law
  plus weak convergence from every initial probability law.
- Tiling side: two distinct stationary probability laws, with no translation invariance added. That
  is correct, because the printed statement does not claim it and the proof's clone-started law is
  not translation invariant.
- Non-tiling side: `AllTimeCFTP` plus `IsErgodic`.
- Common neighbourhood: stated literally, true by `rfl`.

The Z^4 undecidability corollary (`Z4MachineCorollary`) carries no hypothesis. Its reduction clause
is exactly `FNR.DominoReduction`, which is already proved (`FNR.domino_reduction`, re-exported in
`Reduction.lean`). No Z^3 statement and no Kari hypothesis exist (grep of every Lean file).

## Vacuity

None found.
- `noiseLaw` and `noiseLaw₂` use Mathlib's `infinitePi`, which is a genuine probability product here
  because `0 < e ≤ e₀ ≤ 1`. So the `∀ᵐ` in `AllTimeCFTP` is not trivially true.
- `IsErgodic`, `IsStationary` and `WeakTendsto` are the predicates the frozen Z^6 core used to prove
  both directions of Theorem D. They are therefore neither trivially true nor trivially false.
- `HasTwoInvariantLaws` demands `μ ≠ ν`.
- `AllTimeCFTP` holds trivially only for `R = ∅`, where the alphabet is a singleton, as in the paper.

## Harmless deviations worth recording (no change required)

1. **`AllTimeCFTP` adds `∀ t : ℤ` inside the almost-sure quantifier.** The printed sentence names
   no time, but the proof of `ld:cftp` fixes an arbitrary `t`. Placing `∀ t` and `∀ O` inside one
   `∀ᵐ` is equivalent to the printed per-window form, by countability of `ℤ × Finset ℤ⁴`.
   `∃ n₀, ∀ n ≥ n₀` is equivalent to "in finite time" because the pullback images are nested.
2. **`Z4MachineCorollary` is stronger than the printed sentence.** The printed sentence (proof of
   12.5, last line) says only: fixed-rate undecidability at `e = e₀` on the raw family `R ↦ G_R^(4)`.
   The Lean adds three things:
   - (a) the claim holds at every `e ∈ (0, e₀]`;
   - (b) it is stated on the computably indexed subfamily `G_{W_M}`, together with ergodic ⇔ halts;
   - (c) it adds the positive-rate clause.

   All three are true: they follow from Theorem 12.5, the proved domino reduction, and the Section 2
   noise table. RELAY.md assigned exactly this machine form ("as it follows directly: a computable
   map M ↦ W_M with G^(4)_{W_M} ergodic iff M halts"). The machine form implies the printed
   raw-family sentence at once: a raw decider `h` would make `h ∘ W` a computable halting decider.

## Recommendations (non-blocking; the verdict does not depend on them)

- **R1 (literal printed sentence).** For a statement of record that also contains the printed
  undecidability sentence word for word, add after `Z4MachineCorollary`:
  ```lean
  /-- Proof of Theorem 12.5, last sentence: fixed-rate undecidability on the raw family
  R ↦ G_R^(4) (abstract: "one explicit positive rational replacement rate ... makes ergodicity
  undecidable"). Raw inputs are lists of tiles, as in FNR.ErgodicityUndecidable; no hypothesis. -/
  def Z4RawUndecidable : Prop :=
    ∀ e : ℝ, 0 < e → e ≤ eps0 →
      ¬ ∃ g : List Tile → Bool, Computable g ∧
        ∀ l : List Tile, g l = true ↔ (natCA l.toFinset).IsErgodic e
  ```
  It follows from `Z4MachineCorollary` by composing with `W` (`Computable.comp`). If only the
  printed rate is wanted, specialize it to `e = eps0`.
- **R2 (freeze hygiene).** Remove the two `sorry` stubs (`FLD.Draft.z4`,
  `FLD.Draft.machine_corollary`) from the frozen statement file, or replace them with the proved
  theorems in the proof files. That way no `sorryAx` can reach anything through an import of the
  statement of record. FNR's frozen file holds no theorem bodies.
- **R3 (marking).** The file has no `[choice]` tags, unlike the frozen cores. Its unmarked choices
  are listed in YOUR-TABLE.md and are all harmless:
  - `Option (Fin 2)` cluster labels;
  - planar coordinates first;
  - `Fintype.equivFin` for the alphabet;
  - the ⊥ extension outside `natNbhd`, which is never read;
  - `Classical.choose`, made immaterial by 2·512 > 768;
  - `∀ t` in the CFTP clause;
  - the strengthened corollary.

  Tagging them would match house style.
- **R4 (paper text, outside this read).** The printed abstract, `10-how.tex` line 22 and
  `paper/README.txt` say the Z^4 theorem is not formalized. If this core closes, those sentences
  will need updating in the next version.

## Comparison with STATUS.md ("Statement fidelity choices for QB", items 1 to 5)

| STATUS item | My reading | Agreement |
|---|---|---|
| 1. Exact reuse of FNE Tile/WangSet/Plane/TuringMachine/Halts; FNR TilesPlane/Letter/letterEquiv/cardinal/IsPositiveRatePCA; UND.CA noise, laws, ergodicity, weak convergence from every initial law | Rows 2, 9, 11, 17 to 19 | AGREE |
| 2. site = (u1,u2,P1,P2); Provider = Option(Fin 2) × (Fin 2 → Fin 16); corners 0, 160e1, 160e2; quorum 512; 768 providers | Rows 4 to 6, 10, 13 to 16; I also checked disjointness and injectivity of `offset` (so 768 providers = 768 offsets) | AGREE |
| 3. Two invariant laws via IsStationary and probability measures; no translation invariance added | Row 21 | AGREE |
| 4. AllTimeCFTP: all observation times and windows inside one a.s. quantifier, uniform over starts and long horizons; "makes the printed simultaneity explicit" | Row 22 | AGREE in substance. Small disagreement of description: `∀ t` is an addition beyond the printed words, not just a clarification. It is equivalent to the printed form; BLUEPRINT.md describes it correctly ("obtainable by countable intersections and time shifts"). |
| 5. Machine corollary: one computable W before e and M, the domino specification, positive-rate property, no computable decider; list-coded tile map | Rows 25 and 26 | AGREE on content. DISAGREEMENT (record-keeping only): STATUS and BLUEPRINT do not say that this proposition is stronger than the printed sentence (all rates, machine subfamily, positive-rate clause) or that the literal raw-family sentence is not stated as its own proposition. See harmless deviation 2 and R1. |
| "The draft includes every sentence of Theorem 12.5" (Outcome) | Rows 20 to 24 | AGREE |
| "No Z3 work or Kari hypothesis has been introduced" | Row 27 (grep confirms) | AGREE |
| "The isolated FLD.Draft theorem section contains the two temporary stubs" | Row 28 | AGREE; see R2 for the freeze |

No fidelity point in STATUS.md is wrong. The only additions from this read are the ones above: the
strengthening of the corollary should be recorded, and R1 to R3 are optional.
