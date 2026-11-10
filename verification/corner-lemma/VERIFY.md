# Corner lemma: programs, outputs and controls

These files prove the finite statement of the corner lemma (Section 9, Lemma "Corner lemma", label `thr:corner`). The paper cites the two programs `ENGINE-PALETTE-A.py` and `CORNERS-B.py`.

## The finite statement

- Box `[0,32]^2`, centre `(16,16)`: the paper's `V_16` shifted by an even vector. The box does not wrap around; neighbours outside it impose nothing.
- Thin types: `a`, `c`, `d`, `b` on the sites with `(x mod 2, y mod 2)` equal to `(0,0)`, `(1,0)`, `(0,1)`, `(1,1)`.
- Centre: the single letter `(thin a, corner k, black A, bits 1,1)`, for each of the four corners `k`.
- Every other site: all letters of the 276-letter scaffold with that thin type, except the four letters `(thin a, corner, black A, bits 0,0)`. Lines and letters with unequal bits are kept.
- Arc consistency on the four cardinal directions: delete a letter that has no matching letter at some neighbour inside the box, until nothing changes.
- Claim: for each corner `k`, every list ends empty.
- Positive control: the same computation with the four letters kept. No list ends empty, and every value of a known legal 33 x 33 pattern survives.

## Files

| File | What it is |
|---|---|
| `ENGINE-PALETTE-A.py` | First program. Builds the alphabet from the base-tile eligibility rules; per-letter compatibility masks; revisits one site at a time from a queue. Run with `--critical-only` for the 8 cases of the lemma (4 corners, forbidden and control). In each control it builds the legal pattern below and asserts that all its values survive. |
| `ENGINE-PALETTE-A-critical-controls.results.json` | Output of the `--critical-only` run: the 8 cases, with every final list (46 MB). |
| `ENGINE-PALETTE-A_--critical-only.run.json` | Resource receipt of that run. |
| `CORNERS-B.py` | Second program, written separately. Builds the alphabet from named line and black-type tables; colour classes in E,N,W,S order; synchronous sweeps over the box. 8 cases. |
| `CORNERS-B.results.json`, `CORNERS-B.run.json` | Its output (25 MB) and resource receipt. |
| `CORNERS-B-CONTROLS.py` | The second program with the legal-pattern check added to each control. |
| `CORNERS-B-CONTROLS.results.json`, `CORNERS-B-CONTROLS.run.json` | Its output (25 MB) and resource receipt. |
| `ENGINE-C.py` | A third implementation, written separately by a reviewer from the letter tables alone: string edge colours and an AC-3 arc queue. Same 8 cases, plus the forbidden cases without the imposed thin types (they also empty), plus the least emptying box side (13). |
| `ENGINE-C.results.json`, `ENGINE-C.run.json` | Its output and resource receipt. |
| `resource_guard.py` | Memory guard imported by every program: caps the process at 1 GB, refuses to start below 9 GiB of free memory, writes `<script>.run.json` at exit. On other systems it does nothing. |

The legal pattern of the controls is the restriction to `[16,48]^2` of `sigma^3(o)`, a pattern on `[0,64)^2`, with outer letter `o` equal to `(d, <g0,g1>, D, 0, 0)`, `(a, corner a, A, 0, 0)`, `(c, <g0,g1>, B, 0, 0)` and `(b, corner a, A, 0, 0)` for the root corners `a`, `b`, `c`, `d`. Its value at `(32,32)` is the root.

## Expected results

All programs, all four corners (CORNERS-B.py prints only the final counts and sweeps; the initial and pair counts are printed by the other two):

- 1089 sites; at most 1089 x 276 = 300564 list entries; 4 x 276^2 = 304704 directional pairs, of which 4496 are compatible.
- Forbidden case: 76801 entries after the thin-type filter, 0 at the end, 1089 empty sites. In `CORNERS-B.py` the centre list empties in sweep 20 and the fixed point is reached in sweep 45.
- Control: 77953 entries after the filter, 57290 at the end, no empty site, the root kept, all 1089 values of the legal pattern kept (`positive_control_word_checked` in A, `known_actual_control_patch_verified` in B-CONTROLS, `control_word_cells_lost: 0` in C).
- `ENGINE-PALETTE-A.py` also prints a SHA-256 of the final lists (`domain_sha256`); it is `86aff1859b6f484df316f3cb732e10ec08367affa46201182fb03c020520b0b8` for the four forbidden cases.

## How to run

Requirements: Python 3.10 or later, standard library only. On Windows the guard caps memory; elsewhere it does nothing.

The programs overwrite their result and receipt files next to the script. Copy this folder to a scratch directory first, and run there, one process at a time:

    python -I -B ENGINE-PALETTE-A.py --critical-only
    python -I -B CORNERS-B.py
    python -I -B CORNERS-B-CONTROLS.py
    python -I -B ENGINE-C.py

Each run takes a few seconds and less than 30 MB of memory. Compare the printed summary lines with the expected results above. The result files list every final list, so they are large; compare their scalar fields, not the whole files.

Without `--critical-only`, `ENGINE-PALETTE-A.py` also runs seven exploratory cases (small tori and an unrestricted box) and writes `ENGINE-PALETTE-A-results.json`. The paper does not use those cases, and that file is not included here.
