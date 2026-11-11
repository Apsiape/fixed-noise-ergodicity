# Untrusted producer, analysis pass: synchronous arc consistency on the box V_r around a root,
# with the letter table dumped from Lean (Letter.letters order and colour codes).
# Usage: python -I -B scripts/corner/analyze.py LETTERS.txt RADIUS
#   prints, per corner, the number of rounds, whether the root is deleted, and the entries.
# LETTERS.txt: the output of `lean scripts/corner/Dump.lean` (with LEAN_PATH from scripts/env.sh).
import sys
L = [l.split() for l in open(sys.argv[1]).read().strip().split('\n')]
assert len(L) == 276
thin = [l[0] for l in L]; thick = [l[1] for l in L]; black = [l[2] for l in L]
b1 = [int(l[3]) for l in L]; b2 = [int(l[4]) for l in L]
cN = [int(l[5]) for l in L]; cE = [int(l[6]) for l in L]; cS = [int(l[7]) for l in L]; cW = [int(l[8]) for l in L]
def mask(p): return sum(1 << i for i in range(276) if p(i))
cls = {s: [mask(lambda i, c=c: code[i] == c) for c in range(64)] for s, code in (('N', cN), ('E', cE), ('S', cS), ('W', cW))}
# supp pairs: direction -> list of (mask of letters at u with code c on the facing side, mask at neighbour with code c on the opposite side)
PAIRS = {'e1': [(cls['E'][c], cls['W'][c]) for c in range(64)], 'e1p': [(cls['W'][c], cls['E'][c]) for c in range(64)],
         'e2': [(cls['N'][c], cls['S'][c]) for c in range(64)], 'e2p': [(cls['S'][c], cls['N'][c]) for c in range(64)]}
VEC = {'e1': (1, 0), 'e1p': (-1, 0), 'e2': (0, 1), 'e2p': (0, -1)}
def supp(d, A):
    s = 0
    for (m, o) in PAIRS[d]:
        if o & A: s |= m
    return s
def thin_rule(x, y): return {(0, 0): 'a', (1, 0): 'c', (0, 1): 'd', (1, 1): 'b'}[(x % 2, y % 2)]
def root_idx(k): return [i for i in range(276) if thin[i] == 'a' and thick[i] == 'C' + k and b1[i] == 1 and b2[i] == 1][0]
def D(k, x, y):
    if (x, y) == (0, 0): return 1 << root_idx(k)
    return mask(lambda i: thin[i] == thin_rule(x, y) and not (thin[i] == 'a' and thick[i][0] == 'C' and b1[i] == 0 and b2[i] == 0))
def run(k, r, maxrounds=200):
    sites = [(x, y) for y in range(-r, r + 1) for x in range(-r, r + 1)]
    A = {s: D(k, *s) for s in sites}
    hist = [dict(A)]
    for t in range(1, maxrounds):
        B = {}
        for (x, y) in sites:
            m = A[(x, y)]
            for d, (dx, dy) in VEC.items():
                n = (x + dx, y + dy)
                if n in A: m &= supp(d, A[n])
            B[(x, y)] = m
        if B == A: break
        A = B; hist.append(dict(A))
        if not (A[(0, 0)] >> root_idx(k)) & 1: break
    return sites, hist
if __name__ == "__main__":
    r = int(sys.argv[2])
    for k in 'abcd':
        sites, hist = run(k, r)
        T = len(hist) - 1
        rootdead = not (hist[-1][(0, 0)] >> root_idx(k)) & 1
        changed = [sum(1 for s in sites if hist[t][s] != hist[t - 1][s]) for t in range(1, T + 1)]
        ent0 = sum(bin(v).count('1') for v in hist[0].values()); entT = sum(bin(v).count('1') for v in hist[-1].values())
        print(k, 'r', r, 'rounds', T, 'root dead', rootdead, 'entries', ent0, '->', entT, 'changed sites total', sum(changed), changed)
