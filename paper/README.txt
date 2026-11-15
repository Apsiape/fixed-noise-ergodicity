Forgetting under noise is undecidable
Seth Douglas and Nidhal Mghirbi
Version 3.0.0, November 2026

main.pdf is the compiled 170-page preprint. main.tex inputs preamble-core.tex and
sections/. abstract.txt gives the same abstract as plain text.

Build from this directory:

    python -I -B guarded_build.py --build-dir ../build-paper

Use a new or empty directory within the release folder. Requires Python 3,
pdflatex and the LaTeX packages in preamble-core.tex. The wrapper calls the
adjacent Windows resource guard, which requires at least 9 GiB free and
caps process/job memory at 1,000,000,000 bytes. Wait and retry if it refuses;
run one Python process at a time. It executes unchanged build.py in the
same Python process. The strict driver runs three pdflatex passes without
shell escape or package installation and rejects warnings, unresolved
references and overfull or underfull boxes. The bibliography is inline.
On other operating systems the same strict driver can be run directly:

    python -I -B build.py --build-dir ../build-paper

Reading order: Sections 2-3 prove the natural Z^6 classification and its
consequences; Sections 4-11 retain the inspector and machine route;
Section 12 proves the lower-dimensional classifications, rates and Gibbs
supplement; Section 13 lists open problems; Section 14 proves the
conditional translation-invariant degree. Appendix C records Lean scope.

New in 3.0.0: natural-rule intervals 0<epsilon<=10^-24 on Z^6 and
0<epsilon<=10^-30 on Z^4 and Z^3, with unchanged rules and geometry.
The Z^6 memory error bound is p_*=10^-4, with 2epsilon recovered for
epsilon<=10^-40, and its coalescence slope is (3/16)log 2. The lower-
dimensional exponent is 1/24000; exponent 1/4 is retained through
10^-4535 with the same effective input-dependent prefactor.

Under the published-source condition C_T, one computable family on Z^6,
range at most 11, has Pi^0_2-complete TI stationary uniqueness at each
fixed rational 0<epsilon<=10^-22. Its normalized positive rational factors
give Pi^0_2-complete fully TI Gibbs uniqueness on Z^7. Rice Lemma 6.1
already gives the same Z^6 family and dichotomy, and Rice Theorem C (r=1)
the TI stationary degree on Z^7, at 160000^-101 under C_T. Section 14 adds
the rate interval, explicit Z^6 degree, Z^7 TI Gibbs degree and full proof.
Open problem 13.2 remains open as stated; Section 14 settles its TI variant.

The natural Lean cores cover only the version 2.2.0 intervals:
0<epsilon<=(2(18q)^2)^-200 on Z^6 and 0<epsilon<=382205952^-33720
on Z^4. The Z^8 machine core and 490000^-99 interval are unchanged.
The enlarged intervals and Section 14 are paper proofs with exact
arithmetic. The sibling verification-thresholds/ folder supplies the
portable 75-check certificate, recorded output and exact scope.
