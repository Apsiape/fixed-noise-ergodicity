Forgetting under noise is undecidable
Seth Douglas and Nidhal Mghirbi
Version 2.0.0, November 2026

Build: python -B build.py [--build-dir NEW_OR_EMPTY_DIRECTORY]
Requires Python 3, pdflatex and the LaTeX packages named in preamble-core.tex. No BibTeX run is
needed; the bibliography is inline (sections/references.tex). The build runs pdflatex three times
without shell escape and rejects warnings, unresolved references and overfull or underfull boxes.
main.pdf is the compiled preprint (148 pages). main.tex inputs preamble-core.tex and the files in
sections/. abstract.txt is the abstract as plain text.
Some recent LaTeX releases apply a first-aid patch to cleveref (hook chunk firstaid/cleveref) that
names every theorem-like environment "Theorem" in cross-references. build.py removes that patch
for the run; with plain "pdflatex main.tex" such releases may print "Theorem" where the paper
means Proposition, Lemma or Corollary. The mathematics is unaffected either way.

Reading order: Section 2 proves the natural classification on Z^6 (Theorem 2.1); Section 3 gives
its consequences, including Theorem A on Z^6 (Corollary 3.1). Sections 4-6 keep the inspector
theory and Sections 7-11 the machine family. Section 12 proves the weighted-cover saturation
obstruction, the all-path density lemma, the natural raw-Wang theorem on Z^4 (Theorem 12.5) and
the transverse-quorum lift of Kari's nilpotency reduction on Z^3 (Theorem 12.11); these are
Theorems E and F of the introduction. Section 13 lists open problems. Appendix C describes both
Lean cores.

The Z^4 rule applies to every finite raw Wang set; the Z^3 rule assumes north/east edge-colour
determinism. Both use the tiles plus one blank as alphabet, one common finite neighbourhood per
family, whole-symbol uniform replacement, and the common sufficient interval
0 < epsilon <= 382205952^(-33720). Their conclusions are qualitative: all-start finite-window
coupling from the past on non-tiling inputs and two distinct invariant laws on tiling inputs.
Exponential forgetting, all-Gibbs uniqueness, robustness and formalization are asserted only for
the Z^6 construction.

Formal verification: ../lean-natural/ holds the Z^6 natural-rule core and ../lean/ the Z^8
machine-family core of version 1.4.0. The natural core verifies both sentences of Theorem D
(Theorem 2.1 without its coalescence bound), Theorem A on Z^6, all of Corollary 3.1, the domino
reduction and the undecidability of the domino problem, without named hypotheses. The coalescence
bound, nilpotency, the other Section 3 consequences and the Z^4 and Z^3 theorems are not formalized.
Pins: Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; only propext,
Classical.choice and Quot.sound are used. The reused cores are public: the lean/ folders of this
paper's version 1.4.0, of the noise-diagram paper's version 1.2.0 (DOI 10.5281/zenodo.24174445) and
of the hard-model paper's version 1.2.0. ../lean-natural/README-ARXIV.md gives reproduction;
vendor/ is fetched, not shipped.

One finite lemma of the machine route (Section 11) is a computation; its programs and outputs are
in ../verification/corner-lemma/. The lower-dimensional proofs have no computed premise. No
publication or submission is performed by the build.
