Forgetting under noise is undecidable
Seth Douglas and Nidhal Mghirbi
Version 2.2.0, November 2026

main.pdf is the compiled 155-page preprint.
main.tex inputs preamble-core.tex and the files in sections/. abstract.txt
gives the same abstract as plain text.

Build: python -I -B build.py --build-dir NEW_OR_EMPTY_DIRECTORY
Requires Python 3, pdflatex and the LaTeX packages in preamble-core.tex.
The bibliography is inline; no BibTeX run is needed. The driver runs pdflatex
three times without shell escape or package installation and rejects warnings,
unresolved references and overfull or underfull boxes. It removes the cleveref
first-aid hook that otherwise misnames theorem-like cross-references on some
LaTeX releases. Use a build directory within your authorized output area.

Reading order: Section 2 proves the natural classification on Z^6 (Theorem 2.1);
Section 3 gives its consequences and Theorem A on Z^6 (Corollary 3.1).
Sections 4-6 retain the inspector theory and Sections 7-11 the machine family.
Section 12 proves saturation, all-path density, the raw-Wang classification on
Z^4 (Theorem 12.5 = Theorem E), and the north/east deterministic family on Z^3
(Theorem 12.11 = Theorem F), followed by the rate and Gibbs supplements.
Section 13 lists open problems. Appendix C describes the three Lean cores.

New in version 2.2.0: Corollary 12.14, after Example 12.13, applies the published
space-time paper v1.2.0 (10.5281/zenodo.24122307), Corollary 13.7 through
Theorem 13.3, to the shared maps of Theorem 12.12. On non-tiling inputs the
normalized interactions on Z^5 (from the Z^4 rule) and Z^4 (from the Z^3 rule)
have exactly one Gibbs measure without an invariance assumption, and
exponential weak spatial mixing in arbitrary finite volumes. The specification
includes every factor meeting the volume, including exterior children.
Distances are sup-norm distances to the whole complement; holes and
disconnected volumes are allowed. Strong mixing and uniform Gibbs constants
as epsilon tends to zero are not claimed. Tiling inputs have at least two
fully space-time translation-invariant Gibbs measures, separated by LIVE after
spatial averaging. At epsilon = e0, Gibbs uniqueness, translation-invariant
Gibbs uniqueness and exponential WSM are undecidable across either family;
Sigma^0_1-completeness is asserted only for the Z^4 checker family.
Lower-dimensional robustness remains outside this release's claims.

Retained from version 2.1.0: Theorem 12.12 gives, on every non-tiling input in
either family, P[the t-step shared map is nonconstant on F]
<= |F| C_R exp(-t/4), for all integers t >= 0 and
0 < epsilon <= e0 = 382205952^(-33720). The exponent and interval are
universal; the effectively findable integer C_R depends on the input and is
independent of epsilon. Example 12.13 shows why non-tiling is essential.
All existing statement and equation numbers and contents are retained; scope
disclaimers are updated. The version 2.1.0 change note remains historical.

Formal verification: the new ../lean-lower/ release package verifies the
qualitative Z^4 natural-rule classification and its direct machine and
raw-family undecidability corollaries. Headline declarations are
FLD.z4_classification, FLD.z4_machine_corollary and FLD.z4_raw_undecidable,
with no named hypotheses. The frozen statement passed a blind fidelity read
(FAITHFUL). Recorded checks: fresh replay of 133 modules, sandboxed comparator,
leanchecker, nanoda with a negative control, and an axiom audit using only
propext, Classical.choice and Quot.sound. The verified package commit is
a471ef3; the final standard-Lake release tag/commit is v2.2.0 (this release).
See ../lean-lower/README-ARXIV.md, REPORT.md, SCOPE.md and STATEMENT-READ.md
and Appendix C for reproduction and scope. No Lean check was run for this
writing revision. The Z^3 family, the lower-dimensional rates and the new
Gibbs corollary are not formalized. The qualitative Z^4 core proves weaker
sparse-root and memory-gap bounds sufficient for its classification; it does
not certify the quantitative LIVE bounds used in Corollary 12.14.

The existing ../lean-natural/ Z^6 core verifies both sentences of Theorem D
(Theorem 2.1 without its coalescence bound), Theorem A, all of Corollary 3.1,
the domino reduction and domino undecidability. The retained ../lean/ Z^8
machine-family core is unchanged. Their scopes remain as described in
Appendix C; the natural core excludes coalescence rates, nilpotency and the
other Section 3 consequences. Recorded pins are Lean 4.35.0 and Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679. This paper folder contains the
manuscript sources and build driver; the Lean packages ship beside it.

The lower-dimensional Gibbs result is a hypothesis check of a shared
published dependency. Its refutation-first check rederived the rate argument
modulo contour and density inputs and the transfer chain, but did not fully
rederive Lemma 12.3's arm construction. The two in-run audits were non-blind
on the key transfer step. See Verification status for the evidence limits.
One finite lemma in the machine route is a computation; its programs and
outputs accompany the release in verification/corner-lemma/. The lower-
dimensional rate and Gibbs proofs have no computed premise. No publication
or submission is performed by the build.
