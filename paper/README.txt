Forgetting under noise is undecidable
Seth Douglas and Nidhal Mghirbi
Version 2.1.0, November 2026

main.pdf is the compiled 152-page preprint. main.tex inputs preamble-core.tex and the
files in sections/. abstract.txt gives the abstract as plain text.

Build: python -I -B build.py [--build-dir NEW_OR_EMPTY_DIRECTORY]
Requires Python 3, pdflatex and the LaTeX packages named in preamble-core.tex.
No BibTeX run is needed; the bibliography is inline in sections/references.tex.
The build runs pdflatex three times without shell escape or package installation.
It rejects warnings, unresolved references and overfull or underfull boxes.
Some recent LaTeX releases apply a cleveref first-aid hook that calls every
theorem-like environment "Theorem". build.py removes that hook for its run, so
Lemma, Proposition and Corollary cross-references retain their proper names.

Reading order: Section 2 proves the natural classification on Z^6 (Theorem 2.1);
Section 3 gives its consequences and Theorem A on Z^6 (Corollary 3.1).
Sections 4-6 retain the inspector theory and Sections 7-11 the machine family.
Section 12 proves the weighted-cover saturation obstruction, all-path density,
the natural raw-Wang theorem on Z^4 (Theorem 12.5), and the transverse-quorum
lift of Kari's nilpotency reduction on Z^3 (Theorem 12.11). These are
Theorems E and F of the introduction. Section 13 lists open problems.
Appendix C describes the existing Lean cores.

New in version 2.1.0: Theorem 12.12, appended at the end of Section 12,
proves for every NON-TILING input in either lower-dimensional family that

  P[the t-step shared map from all starts is nonconstant on F]
      <= |F| C_R exp(-t/4)

for every integer t >= 0, every finite spatial window F, and every
0 < epsilon <= 382205952^(-33720). The exponent and interval are universal.
The integer C_R is effectively findable on non-tiling inputs and independent
of epsilon. The Z^4 family accepts every finite raw Wang set; the Z^3 family
requires north/east determinism. Example 12.13 gives a tileable one-tile NE
input whose all-input coefficient stays at least 1-4 epsilon. Thus the
non-tiling restriction is essential. All previously existing numbered results
and equations retain their numbers.

Theorems E/F, the abstract, version history and verification status include the
new rate. The solved rate question is removed from the open problems.
All-Gibbs uniqueness and robustness are retained for the Z^6 route; they are
not asserted for these Z^4 or Z^3 families.

Formal verification: the Lean appendix is unchanged. The existing natural-rule
core verifies both sentences of Theorem D (Theorem 2.1 without its coalescence
bound), Theorem A on Z^6, all of Corollary 3.1, the domino reduction and the
undecidability of the domino problem, without named hypotheses. The retained
Z^8 machine-family core is also unchanged. Neither the lower-dimensional
classifications nor the new rate are formalized. The coalescence bound,
nilpotency and other Section 3 consequences remain outside the natural core.
The formal packages are in ../lean-natural/ (natural rule, Z^6) and ../lean/
(machine family, Z^8) of the release repository; ../lean-natural/README-ARXIV.md
gives reproduction. This paper folder contains the manuscript sources and build driver. The recorded pins are Lean 4.35.0
and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, with only propext,
Classical.choice and Quot.sound as axioms.

One finite lemma of the machine route in Section 11 is a computation; its
programs and outputs accompany the release in verification/corner-lemma/.
The lower-dimensional rate proof has no computed premise. The build performs
no publication or submission.
