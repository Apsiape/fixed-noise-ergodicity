# Forced word: finite tests for small n

These files test Lemma "The forced word" (Section 9, label `thr:word`) for n = 1 and n = 2. The lemma is proved in the text by chaining the lemmas of Section 9. These computations are a check on that chain, not part of the proof.

## What is computed

- The tests take N = 4^n and an open box around the sites 0 and (N, N). The box does not wrap around; neighbours outside it impose nothing.
- Thin types are fixed with thin phase zero, as in the corner lemma.
- Two pins:
  - site 0 holds a corner letter `(a, corner k, A, 1, 1)` with bit 1;
  - site (N, N) holds a corner letter `(a, corner k', A, 0, 0)` with bit 0.
- Every other site holds all letters of the 276-letter scaffold with its thin type.
- Arc consistency on the four cardinal directions deletes a letter that has no matching letter at some neighbour inside the box, until nothing changes. This yields the largest family of lists that is consistent on the box.
- **Claim tested:** for each of the 16 pairs of corners (k, k'), the largest consistent family is either empty or forces the conclusion of `thr:word`. That is, on a target square [0, 4^n)^2 placed at a pin, every list is the single letter of the word sigma^n(a) predicted by the lemma, where a is a corner letter with bit 1.
- **Controls:**
  - **Legal patch** (n = 1, 2, 3): the pins are taken from a legal substitution pattern. No site empties, the target is forced to the predicted letters, and every value of the legal pattern survives. So the tests are not vacuous.
  - **Ablation** (n = 1, 2, 3): the bit-0 pin is removed. Then 15, 255 and 4,095 target sites, respectively, are no longer singletons. So the second pin carries the information.

## Results (both programs agree)

| Test | Result |
|---|---|
| All 16 corner pairs, n = 1 | 8 empty; in the other 8 all 16 target letters are forced as predicted |
| All 16 corner pairs, n = 2 | 8 empty; in the other 8 all 256 target letters are forced as predicted |
| Legal patch, n = 1, 2, 3 | no target error; 16, 256 and 4,096 predicted singletons; every legal value survives |
| Ablation, n = 1, 2, 3 | 15, 255 and 4,095 target sites not forced |

## What this proves and what it does not

- **It proves:** for each listed box, every family of lists that is consistent on the box and has these pins forces the predicted target letters, or is empty.
  - A plane family that is arc consistent restricts to such a family. So each test also proves the corresponding implication for plane list families with these two pins at displacement (N, N).
- **It does not prove:**
  - the lemma for every n;
  - every displacement in 4^n Z^2;
  - that a surviving finite family extends to the plane;
  - anything about the token game itself.

## Files

| File | What it is |
|---|---|
| `FORCED-WORD-QUEUE.py` | First program. Its own transcription of the letter tables; per-site bitset lists; a site queue. Box [-N, 2N]^2. 38 cases. |
| `FORCED-WORD-QUEUE.results.json`, `FORCED-WORD-QUEUE.run.json` | Its output and resource receipt. |
| `FORCED-WORD-SWEEP.py` | Second program, written separately. Its own transcription; colour-class supports; synchronous sweeps. Box [-N, 2N-1]^2. 38 cases. |
| `FORCED-WORD-SWEEP.json`, `FORCED-WORD-SWEEP.run.json` | Its output and resource receipt. |
| `resource_guard.py` | The memory guard of `../corner-lemma/`, imported by both programs. |

Neither program imports the other or a corner-lemma program. Each builds its own legal substitution witnesses for the controls. Run each with `python FORCED-WORD-QUEUE.py` and `python FORCED-WORD-SWEEP.py` from this folder; each takes under a minute.

They were written during the independent review of version 1.2.0 and are included in version 1.3.0. The results above are from a fresh run in this folder, which matched the review's run case by case.
