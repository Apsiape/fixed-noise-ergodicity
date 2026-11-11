# Forgetting under noise is undecidable: ergodicity of positive-rate cellular automata at a fixed noise rate

Seth Douglas and Nidhal Mghirbi. Version 1.4.0, November 2026. The version 1.4.0 DOI is recorded in the commit that follows the release. Version 1.3.0: [10.5281/zenodo.24115709](https://doi.org/10.5281/zenodo.24115709). Version 1.2.0: [10.5281/zenodo.24105227](https://doi.org/10.5281/zenodo.24105227). Version 1.1.0: [10.5281/zenodo.24104252](https://doi.org/10.5281/zenodo.24104252). Version 1.0.0: [10.5281/zenodo.24102672](https://doi.org/10.5281/zenodo.24102672). Concept DOI (all versions): [10.5281/zenodo.24102671](https://doi.org/10.5281/zenodo.24102671).

**This is a preprint. It has not been peer reviewed.**

## Abstract

Can noise make the long-run behaviour of a cellular automaton predictable? A probabilistic cellular automaton with positive rates, in which every site can take every value with positive probability at every step, is ergodic when it forgets its initial configuration. Deciding ergodicity is known to be impossible when some transitions may have probability zero. We show that positive noise does not restore decidability. There are an explicit rate ε₀ > 0 and a computable family of positive-rate cellular automata on ℤ⁸, each a deterministic local rule followed by uniform random replacement, such that for every noise rate ε in (0, ε₀] the automaton built from a Turing machine M is ergodic if and only if M halts.

The proof links a logical quantity to a physical one. A tile set that tiles the plane makes a noisy quorum rule remember. A tile set whose contradictions can always be cornered by a fixed number of local tokens, a refutation of bounded width in the sense of existential pebble games, makes the same rule forget. We build a computable family of tile sets in which every contradiction that exists can be cornered by three tokens: two hold the phase of a recognizable substitution while the third walks, and the machine runs in a layer closed under intersection. The classification holds on a ball of one fixed total-variation radius around every member, and the theorem on ℤ⁸ is proved in Lean. Further consequences: no computable function bounds how long the ergodic members take to forget; since the forgetting bound holds for all starts at once, uniqueness of the space–time Gibbs measure, with no invariance assumed, and exponential weak spatial mixing are undecidable; and stacking copies of each member gives automata that, undecidably, have either exactly one invariant measure or a continuum of extreme invariant measures.

## What the paper proves

A probabilistic cellular automaton updates every site of a lattice at once. Each site reads a few neighbours and picks its next value at random, from one fixed table. When every entry of that table is positive, nothing is ever forbidden. The automaton is ergodic if it forgets where it started: one invariant measure, reached from every starting law.

- **Theorem A.** There is a total computable map M ↦ R_M from Turing machines to finite Wang tile sets. For every ε in (0, ε₀], with ε₀ = 490000^(−99), the quorum rule of R_M on ℤ⁸, followed by uniform random replacement at rate ε, is a positive-rate automaton that is ergodic if and only if M halts.
- **Theorem B.** For every finite Wang set R, at one rate ε₀ fixed before R:
  - if R tiles the plane, the noisy quorum rule remembers a bit forever;
  - if every contradiction of R can be cornered by j local tokens (k ≥ 2j), the rule forgets its start exponentially fast after a delay set by the refutation.
- **Theorem C.** One computable family of tile sets: R_M tiles exactly when M does not halt, and every halting member is refuted by three tokens. A general argument with a large fixed number of tokens comes first; Section 9 lowers it to three.
- **Robustness (version 1.2.0).** Every probabilistic cellular automaton whose transition table is within total-variation distance ε₀ of a member of the family has the same classification; the radius is the same for every member.
- **Version 1.3.0.** Corrections from an independent review of the whole manuscript (an omitted case in a remark of Section 8.2 and a credit sentence), and finite tests of the forced-word lemma of Section 9.
- **Version 1.4.0.**
  - The forgetting bound holds for all starts at once: one realisation of the noise makes the value at a site the same for every start, outside an event whose probability is exponentially small in the time and which depends on the replacement indicators alone (Corollary 3.12).
  - Through a theorem of our paper on space–time Gibbs states (DOI [10.5281/zenodo.24122307](https://doi.org/10.5281/zenodo.24122307)), the space–time interaction of a halting member has exactly one Gibbs measure, with no invariance assumed, and exponential weak spatial mixing in arbitrary volumes; a nonhalting member has at least two translation-invariant ones (Corollary 8.8).
  - Stacked automata: running each member on parallel copies, each copy reading the next, gives automata on ℤ⁹ with one invariant measure if M halts and a continuum of extreme invariant measures, mixing in time, if M does not (Corollary 8.17).
  - An explicit construction of the one-sided machine M° (Appendix B), and a remark that the corner lemma is needed only at the centre of the box, which already holds on a box of side 13.
  - Corollary 9.21 (Theorem A on ℤ⁸) and its undecidability are proved in Lean 4 with Mathlib (Appendix C); the sources and the records of the comparator check and of two kernel replays are in `lean/`.
- **Corollaries.**
  - One family works at every rate in (0, ε₀], and for other replacement laws.
  - A computable map sends every Wang set to a noisy automaton that is ergodic exactly when the set does not tile.
  - No computable function bounds how long the halting members take to forget.
  - The undecidability has no borderline cases: every halting member forgets exponentially fast, and every other member has memory with amplitude 1 − 2.02ε.
  - On the space–time interactions of the members, uniqueness of the Gibbs measure, uniqueness of the translation-invariant Gibbs measure and exponential weak spatial mixing each hold exactly when M halts, so each is undecidable.
  - Stacked copies of each member have either one invariant measure or a continuum of extreme ones, and no algorithm tells which.

The dimension is 8 and the rate ε₀ = 490000^(−99) is explicit (version 1.1.0; version 1.0.0 had a fixed but uncomputed, very large dimension). One token never suffices; whether two do, which would give ℤ⁶, is the first open problem in the paper.

The proofs build on prior work that the paper credits in detail:
- Toom's contours and the Peierls bounds of Swart, Szabó and Toninelli;
- the checker reduction of Čulik, Pachl and Yu, and of Kari;
- Ollinger's two-by-two substitution;
- local rules for substitutions (Mozes) and recognizability (Mossé, Solomyak);
- pebble games and treewidth (Kolaitis, Vardi, Dalmau);
- closure properties of constraints (Jeavons, Cohen, Gyssens; Feder, Vardi);
- the space–time Gibbs correspondence (Goldstein, Kuik, Lebowitz, Maes);
- the proof assistant Lean 4 and its library Mathlib, for the formal proof.

## Contents and reproduction

- `paper/main.pdf`: manuscript.
- `verification/corner-lemma/`: the one computed lemma (an arc-consistency deletion on a 33 × 33 box, four roots and four positive controls), done by two independently written programs and a third written separately during review, with their outputs and run receipts. Start with `VERIFY.md`.
- `verification/forced-word/`: finite tests of the forced-word lemma of Section 9 for n = 1 and 2 (all sixteen pairs of corner letters, with legal-pattern and ablation controls), by two independently written programs. The lemma is proved in the text; these tests are a check, not part of the proof. See `VERIFY.md` there.
- `lean/`: the formal proof in Lean 4 with Mathlib of Corollary 9.21 (Theorem A on ℤ⁸) and of its undecidability, described in Appendix C of the paper ([release v1.4.0](https://github.com/Apsiape/fixed-noise-ergodicity/tree/v1.4.0/lean)). It holds the sources, the pins of every dependency, the comparator challenge (`Challenge.lean`, which imports only Mathlib), and the records of the sandboxed comparator run, of the replays of the proof by the kernel checkers leanchecker and nanoda, and of the axiom audit. Start with `lean/README.md`.
- `paper/`: LaTeX source (`main.tex`, `preamble-core.tex`, `sections/`), plain-text abstract and a strict build driver. Run `python -B build.py` there with pdflatex installed. The build disables shell escape, runs pdflatex three times and rejects warnings, unresolved references and box defects.
- `SHA256SUMS`: SHA-256 hashes of every shipped file except this manifest. Check with `sha256sum -c SHA256SUMS` from the repository root.

One finite lemma (Section 9) is a computation, carried out by two independently written programs and checked by a third; no other proof uses a computation. The forced-word tests are checks, not proofs. In the Lean formalization, the corner lemma, in the form that the paper uses, is checked by the Lean kernel.

## Citation and rights

See `CITATION.cff` for citation metadata.
Paper and documentation: CC BY 4.0. Scripts and Lean sources (the build script, the programs in `verification/` and the authors' files in `lean/`): MIT or Apache 2.0, at your option. `lean/cache-tool/Requests.lean` is a modified Mathlib file under the Apache License 2.0. See `RIGHTS.md`, the license files and `NOTICE`.
