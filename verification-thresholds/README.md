# Exact numerical certificate for version 3.0.0

Requires Python 3 and its standard library on Windows, macOS or Linux. From this directory run:

    python -I -B independent_arithmetic.py

Use `python3` in place of `python` where that is the Python 3 command. No package installation is needed. The arithmetic script has no operating-system-specific memory guard. Its arrays and integer sizes are bounded in its opening precheck; its conservative numerical working-set bound is 64 MiB. A fresh run prints 75 successful checks. The recorded output is `independent_arithmetic.log`.

The independently written program derives the Eulerian numerators and affine corner gains; checks arm, walk, packing and deterministic geometric constants; certifies the Z^6 threshold 10^-24 and doubled-density robustness estimates; certifies the Z^4/Z^3 threshold 10^-30, density exponents and retained 10^-4535 interval; and derives the degree construction's Newton coefficients and certifies its two estimates at 10^-22. All mathematical comparisons use integers and fractions. Printed decimal approximations are for orientation only. Exponential comparisons use a rational factorial-series upper bound on exp(1). Endpoint monotonicity supplies smaller positive rates.

It checks finite arithmetic only. It does not verify contour/frontier constructions, pathwise probability arguments, the published-source condition C_T, stationary-law extraction, compactness, the Gibbs correspondence, any Lean theorem, or the retained machine-route configuration computation. Those arguments and dependencies are stated in the paper. The enlarged noise intervals and degree theorem are paper proofs with these arithmetic checks; this certificate is not a formal verification of those proofs.
