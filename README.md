# Forgetting under noise is undecidable

Seth Douglas and Nidhal Mghirbi. Version 3.0.0, November 2026. Concept DOI (all versions): [10.5281/zenodo.24102671](https://doi.org/10.5281/zenodo.24102671). Version 2.2.0: [10.5281/zenodo.24207965](https://doi.org/10.5281/zenodo.24207965). Version 2.1.0: [10.5281/zenodo.24178276](https://doi.org/10.5281/zenodo.24178276). Version 2.0.0: [10.5281/zenodo.24176024](https://doi.org/10.5281/zenodo.24176024). Version 1.4.0: [10.5281/zenodo.24126025](https://doi.org/10.5281/zenodo.24126025). Version 1.3.0: [10.5281/zenodo.24115709](https://doi.org/10.5281/zenodo.24115709). Version 1.2.0: [10.5281/zenodo.24105227](https://doi.org/10.5281/zenodo.24105227). Version 1.1.0: [10.5281/zenodo.24104252](https://doi.org/10.5281/zenodo.24104252). Version 1.0.0: [10.5281/zenodo.24102672](https://doi.org/10.5281/zenodo.24102672).

**This is a preprint. It has not been peer reviewed.**

## Abstract

Can ongoing positive noise make the long-term behaviour of a finite local rule decidable? A natural noisy Wang rule is ergodic exactly when its raw tile set does not tile the plane, at every replacement rate up to 10^-24 on Z^6 and 10^-30 on Z^4. A related construction on Z^3 gives the same equivalence for north/east deterministic tile sets. On non-tiling inputs the lower-dimensional all-input nonconstancy probability on a finite window F is at most |F| C_R exp(-t/24000), with an effectively findable input-dependent prefactor uniform in the rate; the exponent 1/4 is retained for rates up to 10^-4535. On those inputs their normalized space-time interactions have uniqueness among all Gibbs measures and exponential weak spatial mixing. Ergodicity, Gibbs uniqueness and exponential weak spatial mixing are therefore undecidable at one fixed rational rate. A different family on Z^6, of fixed range 11, makes uniqueness among translation-invariant stationary laws Π⁰₂-complete at the single rational rate 10^-22, under a stated published-source condition C_T; the corresponding translation-invariant Gibbs problem is Π⁰₂-complete on Z^7. The enlarged intervals are paper proofs with exact arithmetic. Lean covers only the version 2.2.0 intervals of the retained natural-rule cores; the machine-family core is unchanged. Finite forbidden patterns give forgetting bounds, while infinite tilings protect distinct stationary laws.

## What the paper proves

A probabilistic cellular automaton updates every site of a lattice at once. Each site reads a few neighbours and picks its next value at random, from one fixed table. When every entry of that table is positive, nothing is ever forbidden. The automaton is ergodic if it forgets where it started: one invariant measure, reached from every starting law.

The paper's rules read a Wang tile set directly. A finite Wang set R is a set of square tiles with coloured edges; it tiles the plane if copies can cover ℤ² with matching edges. Its alphabet is R plus one blank. Each site checks that its tile matches its four planar neighbours, then a quorum of transverse copies votes, and the output is replaced by a uniformly random letter at a fixed rate ε.

- **Theorem D (ℤ⁶).** For every finite Wang set R and every 0 < ε ≤ ε_* = 10^−24 (version 2.2.0: (2(18q)²)^(−200), q = 5·16⁴), the natural rule G_R on ℤ⁶ is ergodic if and only if R does not tile the plane. If R tiles, there are two distinct translation-invariant stationary laws. Non-tiling sets are forgotten exponentially fast, from all starts at once, with a universal computable slope.
- **Theorem A (ℤ⁶).** There is a total computable map M ↦ W_M from Turing machines to Wang sets such that, at every rate in (0, ε_*], G_{W_M} is ergodic if and only if M halts. Ergodicity at one fixed rate is therefore undecidable.
- **Theorem E (ℤ⁴).** The same equivalence for a natural rule on ℤ⁴, applied to every finite raw Wang set, with three transverse quorum boxes and a 512-of-768 vote, at every 0 < ε ≤ e_0 = 10^−30 (version 2.2.0: 382205952^(−33720)).
- **Theorem F (ℤ³).** For north/east-deterministic Wang sets, a transverse-quorum lift of Kari's 1992 nilpotency reduction gives the same equivalence on ℤ³ at the same rate. With Kari's theorem, ergodicity at one fixed rate is undecidable on ℤ³.
- **Rate on ℤ⁴ and ℤ³ (Theorem 12.12).** For every non-tiling input of either family, the probability that the shared all-start map is still nonconstant on a finite window F after t steps is at most |F|·C_R·exp(−t/24000) on the whole interval (0, 10^−30], and |F|·C_R·exp(−t/4) for rates up to 10^−4535, with an effectively findable prefactor that does not depend on ε. A one-tile example (Example 12.13) shows that the non-tiling restriction is needed.
- **All-Gibbs uniqueness on ℤ⁴ and ℤ³ (version 2.2.0, Corollary 12.14).** For non-tiling inputs of either family, the normalized space–time interaction (on ℤ⁵, respectively ℤ⁴) has exactly one Gibbs measure, with no invariance assumed, and exponential weak spatial mixing in arbitrary finite volumes; tiling inputs give at least two Gibbs measures invariant under every translation. At one fixed rational rate, Gibbs uniqueness and exponential weak spatial mixing are therefore undecidable in both families. The corollary applies Corollary 13.7 of the authors’ space–time paper to the rate of Theorem 12.12.
- **Why the dimension came down.** A saturation theorem shows that the coherence estimate used on ℤ⁶ cannot work below six dimensions. Theorems E and F replace it with an amortized coherence argument and an all-path density lemma. Their conclusions are coupling from the past on non-tiling inputs, with the exponential rate of Theorem 12.12, and two invariant laws on tiling inputs; robustness is proved for the ℤ⁶ rule only; all-Gibbs uniqueness on ℤ⁴ and ℤ³ is Corollary 12.14.
- **Consequences of Theorem D.** Nilpotency of G_R exactly when R does not tile; exactly one Gibbs measure and exponential weak spatial mixing on the space–time interaction for non-tiling R; robustness of radius ε_* on the same neighbourhood; ergodicity Σ⁰₁-complete and non-ergodicity Π⁰₁-complete at a fixed rational rate; no computable forgetting time; a stacked rule on ℤ⁷ with one invariant measure or a continuum of extreme ones.
- **Degree of translation-invariant uniqueness (version 3.0.0, Section 14).** Under a stated published-source condition C_T (Törmä 2015, Lemma 25, Corollary 26 and Lemmas 27–29 as published), a different family on ℤ⁶, of fixed range 11, makes uniqueness among translation-invariant stationary laws Π⁰₂-complete at the single rational rate 10^−22; the corresponding translation-invariant Gibbs problem is Π⁰₂-complete on ℤ⁷. The same ℤ⁶ dichotomy at the rate 160000^(−101) is Lemma 6.1 of the authors' Rice paper (doi:10.5281/zenodo.24241164); this version adds the rate interval, the explicit degree statements, the Gibbs degree and the full proof. Open problem 13.2 (the degree of all-law ergodicity) stays open.
- **Kept from version 1.4.0.** The inspector theory (Theorem B, token refutability), the machine family on ℤ⁸ (Theorem C and the machine-family theorem), and every other proved statement of version 1.4.0.

**Formal verification.** Theorem D (both sentences, without its coalescence bound), Theorem A on ℤ⁶, Corollary 3.1, the domino reduction and the undecidability of the domino problem are proved in Lean 4 with Mathlib in `lean-natural/`, with no named hypotheses. The domino reduction is proved from the paper's own machine family, so Berger's and Robinson's theorem is not assumed. The qualitative ℤ⁴ classification (Theorem E = Theorem 12.5) and its two undecidability corollaries are proved in Lean in `lean-lower/` (version 2.2.0), with no named hypotheses. The ℤ⁸ machine-family core of version 1.4.0 is in `lean/`. Theorem F, the rates of Theorem 12.12 and Corollary 12.14 are not formalized. Every Lean target covers only the version 2.2.0 intervals (2(18q)²)^(−200) on ℤ⁶ and 382205952^(−33720) on ℤ⁴; the enlarged intervals of version 3.0.0 and Section 14 are paper proofs, with their numerical inequalities certified by exact arithmetic in `verification-thresholds/`.

The proofs build on prior work that the paper credits in detail: Toom's contours and their charge-arm form (Berman and Simon; Gács); the checker reduction of Čulik, Pachl and Yu, and of Kari; Kari's undecidability of the domino problem for deterministic tile sets; Berger's and Robinson's domino problem; Toom's eroder criterion; Ollinger's substitution; local rules and recognizability (Mozes; Mossé, Solomyak); pebble games (Kolaitis, Vardi, Dalmau); the space–time Gibbs correspondence (Goldstein, Kuik, Lebowitz, Maes); and the proof assistant Lean 4 with Mathlib.

## Changes in 3.0.0

- Much larger noise intervals: Theorems D and A on ℤ⁶ now hold at every rate up to 10^−24 (was about 10^−2768), and Theorems E and F on ℤ⁴ and ℤ³ up to 10^−30 (was about 10^−289395). The new counting bounds distinct noise-flag positions along a walk instead of witness shapes, with pairwise first-edge accounting in the arm construction (arm coefficients 16 on ℤ⁶ and 96/13 on ℤ⁴; new Lemmas 2.3A–2.3C). The memory bound of Lemmas 2.4 and 2.13 becomes p_* = 10^−4 (every later use needs only p < 1/4), the robustness radius of Corollary 3.5 becomes 10^−24, and Theorem 12.12 has the two-case rate above. The numerical inequalities are certified by an independently written exact-arithmetic program in `verification-thresholds/`.
- Section 14 (new) and Appendix D: the degree of translation-invariant uniqueness, as above.
- Credits added: Sandhu's independent fixed-temperature Gibbs uniqueness result (doi:10.5281/zenodo.23983514), Gayral–Sablik–Taati, Törmä's Proposition 48, and the authors' Rice paper.
- Every earlier statement number is unchanged; the Lean folders are unchanged and their statements keep the version 2.2.0 intervals.

## Changes in 2.2.0

- Corollary 12.14 (new, after Example 12.13): exactly one Gibbs measure and exponential weak spatial mixing for the non-tiling inputs of the ℤ⁴ and ℤ³ families, at least two translation-invariant Gibbs measures for tiling inputs, and undecidability of Gibbs uniqueness at one fixed rate. The sentences that said all-Gibbs uniqueness was not asserted below six dimensions are revised accordingly.
- New Lean core in `lean-lower/` (Appendix C): Theorem E (Theorem 12.5) and its two undecidability corollaries, with no named hypotheses, a sandboxed comparator run, two kernel replays and an axiom audit; its statement file passed a blind fidelity read.
- All three Lean folders now build from a fresh clone with `lake exe cache get` and `lake build`; their proof files are unchanged.
- No existing statement or number changes.

## Changes in 2.1.0

- Theorem 12.12 (new, appended to Section 12): the exponential rate |F|·C_R·exp(−t/4) for every non-tiling input of the ℤ⁴ and ℤ³ families, and Example 12.13 showing that the non-tiling restriction is needed. Theorems E and F, the abstract and the verification account include the rate; the rate question is removed from the open problems. No existing statement or number changes, and the Lean cores are unchanged. The rate is not formalized.

## Changes in 2.0.0

- The natural rule (Theorem D) and its complete proof now lead, followed by its consequences. The inspector theory and the machine family follow; every proved statement of version 1.4.0 is kept with its content. The old Theorem A on ℤ⁸ is now called the machine-family theorem.
- New: Theorems D and A on ℤ⁶ and their consequences; Theorems E and F on ℤ⁴ and ℤ³ (Section 12); the saturation theorem. Problem 10.3 of version 1.4.0 is answered; the dimension problem is restated (fixed-rate undecidability now holds on ℤ³; ℤ² and ℤ¹ are open).
- New Lean core in `lean-natural/` (Appendix C).

## Contents and reproduction

- `paper/main.pdf`: the manuscript (170 pages).
- `paper/`: the LaTeX source (`main.tex`, `preamble-core.tex`, `sections/`), the plain-text abstract and a strict build driver. Run `python -B build.py` there with pdflatex installed. The build disables shell escape, runs pdflatex three times and rejects warnings, unresolved references and box defects.
- `lean-natural/`: the Lean 4 core of the natural rule on ℤ⁶ (sources, frozen statement file, comparator challenge, axiom audit, evidence and report). See `lean-natural/README.md`.
- `lean-lower/`: the Lean 4 core of the natural rule on ℤ⁴, Theorem E (sources, frozen statement file, comparator challenge, axiom audit, evidence and report). See `lean-lower/README.md`.
- `lean/`: the Lean 4 core of the machine family on ℤ⁸ (version 1.4.0, proofs unchanged). See `lean/README.md`.
- Both Lean folders build from a fresh clone with `lake exe cache get` then `lake build`. Mathlib is a pinned Git requirement; the proof cores that `lean-natural/` reuses are shipped as local packages in `lean-natural/deps/`.
- `verification-thresholds/`: the exact-arithmetic certificate of the version 3.0.0 thresholds and rates (75 exact checks; standard-library Python, any operating system). Its README says what it checks and what it does not.
- `verification/corner-lemma/`: the one computed lemma of the machine route, by two independently written programs and a third written during review. Start with `VERIFY.md`.
- `verification/forced-word/`: finite tests of the forced-word lemma of the machine route, by two independently written programs; they are checks, not part of the proof.
- `SHA256SUMS`: SHA-256 hashes of every shipped file except this manifest. Check with `sha256sum -c SHA256SUMS` from the repository root.

## How it was checked

The paper's AI note and its "Verification status" section give the full account, version by version. The work used a combination of AI models (including Claude Opus 5.5, GPT-6.1 Sol and GPT-6 Astra), directed by the authors. Each new result was checked refutation-first by a model of a different developer from the one that found it, and every computed or numerical step was checked by independently written programs; the Lean cores have frozen statement files read blind against the paper. For version 3.0.0 the new thresholds were re-derived by an independent cross-family check with its own exact arithmetic, the degree result was checked cross-family, and the written version had a cross-family text review and a final readback. The authors have not independently verified the new mathematical arguments; they chose the questions, directed the work and are responsible for the claims.

## Citation and rights

See `CITATION.cff` for citation metadata.
Paper and documentation: CC BY 4.0. Scripts and Lean sources (the build script, the programs in `verification/` and the authors' files in `lean/` and `lean-natural/`): MIT or Apache 2.0, at your option. `lean/cache-tool/Requests.lean` is a modified Mathlib file under the Apache License 2.0. See `RIGHTS.md`, the license files and `NOTICE`.
