# Engine C: a third implementation, written separately from the letter tables (Section 5 and Appendix A of the paper).
# Independent of engines A and B: string edge colours, explicit compatible-pair
# sets, classic AC-3 arc queue over Python sets.
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import resource_guard
GUARD = resource_guard.guard()
for v in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[v] = '1'
import json, collections, time

# ---- alphabet, from the text ----
THIN = {  # N,S,E,W
    'a': ('R0', 'G2', 'R1', 'G3'),
    'b': ('G0', 'R2', 'G1', 'R3'),
    'c': ('R2', 'G0', 'G3', 'R1'),
    'd': ('G2', 'R0', 'R3', 'G1'),
}
# thick corner endpoints are those of thin d,a,c,b for corners a,b,c,d
CORNER = {'a': THIN['d'], 'b': THIN['a'], 'c': THIN['c'], 'd': THIN['b']}
BLACK = {  # N,S,E,W bits
    'a': (0, 1, 0, 1), 'b': (1, 0, 0, 0), 'c': (1, 0, 1, 1),
    'd': (1, 1, 1, 0), 'e': (0, 0, 1, 0),
}
VS = ['R0', 'R2', 'G0', 'G2']
HS = ['R1', 'R3', 'G1', 'G3']
THICK = [('C', k) for k in 'abcd'] + [('L', v, h) for v in VS for h in HS]

def thick_edges(K):
    if K[0] == 'C':
        return CORNER[K[1]]
    return (K[1], K[1], K[2], K[2])

def base_allowed(T, K, B):
    if K[0] == 'C':
        return T in ('a', 'b') and B == 'a'
    V, H = K[1], K[2]
    c1 = (B == 'b' and V != 'R0')
    c2 = (B == 'c' and V != 'R2')
    c3 = (B == 'd' and H != 'R3')
    c4 = (B == 'e' and H != 'R1')
    if T == 'a':
        return c1 or c2 or c3 or c4
    if T == 'c':
        return c1 or c2
    if T == 'd':
        return c3 or c4
    return False

BASE = [(T, K, B) for T in 'abcd' for K in THICK for B in 'abcde' if base_allowed(T, K, B)]
LET = []
for (T, K, B) in BASE:
    for X in (0, 1):
        for Y in (0, 1):
            if T in 'bc' and X != 0: continue
            if T in 'bd' and Y != 0: continue
            if K[0] == 'C' and X != Y: continue
            if K[0] == 'L' and K[1][0] == 'R' and K[2][0] == 'R' and X == Y: continue
            LET.append((T, K, B, X, Y))
assert len(BASE) == 104, len(BASE)
assert len(LET) == 276, len(LET)
cnt = collections.Counter(l[0] for l in LET)
assert (cnt['a'], cnt['b'], cnt['c'], cnt['d']) == (184, 4, 44, 44), cnt

def edge(l, d):  # d in 'NSEW'; returns a string colour
    T, K, B, X, Y = l
    i = 'NSEW'.index(d)
    bit = X if d in 'NS' else Y
    return '%s|%s|%d|%d' % (THIN[T][i], thick_edges(K)[i], BLACK[B][i], bit)

N = len(LET)
# compat[d][i] = set of j that may sit in direction d of i
DIRS = {'N': (0, 1, 'S'), 'S': (0, -1, 'N'), 'E': (1, 0, 'W'), 'W': (-1, 0, 'E')}
compat = {}
pairs = 0
for d, (dx, dy, od) in DIRS.items():
    compat[d] = []
    for i in range(N):
        s = frozenset(j for j in range(N) if edge(LET[i], d) == edge(LET[j], od))
        compat[d].append(s)
        pairs += len(s)
print(json.dumps({'engine': 'C', 'letters': N, 'base': len(BASE), 'directional_pairs': pairs}), flush=True)

def F(t):
    return {'a': 'b', 'b': 'd', 'c': 'c', 'd': 'a'}[t]

def ac(lists, side):
    """AC-3 on a non-wrapping side x side box; lists: dict (x,y)->set. Returns rounds of arc revisions."""
    q = collections.deque()
    inq = set()
    for (x, y) in lists:
        for d, (dx, dy, od) in DIRS.items():
            if (x + dx, y + dy) in lists:
                q.append(((x, y), d)); inq.add(((x, y), d))
    revs = 0
    while q:
        arc = q.popleft(); inq.discard(arc)
        (x, y), d = arc
        dx, dy, od = DIRS[d]
        nb = (x + dx, y + dy)
        Lnb = lists[nb]
        keep = {i for i in lists[(x, y)] if not compat[d][i].isdisjoint(Lnb)}
        if keep != lists[(x, y)]:
            lists[(x, y)] = keep
            revs += 1
            # every neighbour of (x,y) must re-check its arc toward (x,y)
            for d2, (ex, ey, od2) in DIRS.items():
                m = (x + ex, y + ey)
                if m in lists:
                    a2 = (m, od2)
                    if a2 not in inq:
                        q.append(a2); inq.add(a2)
    return revs

def thin_at(x, y, cx, cy):
    return {(0, 0): 'a', (1, 0): 'c', (0, 1): 'd', (1, 1): 'b'}[((x - cx) % 2, (y - cy) % 2)]

def corner_case(root_corner, forbid, side=33, impose_phase=True):
    c = side // 2
    root = LET.index(('a', ('C', root_corner), 'a', 1, 1))
    lists = {}
    for x in range(side):
        for y in range(side):
            s = set()
            for i, l in enumerate(LET):
                if impose_phase and l[0] != thin_at(x, y, c, c):
                    continue
                if forbid and l[0] == 'a' and l[1][0] == 'C' and l[3] == 0 and l[4] == 0:
                    continue
                s.add(i)
            lists[(x, y)] = s
    lists[(c, c)] = lists[(c, c)] & {root}
    init = sum(len(s) for s in lists.values())
    revs = ac(lists, side)
    fin = sum(len(s) for s in lists.values())
    empty = sum(1 for s in lists.values() if not s)
    return {'root_corner': root_corner, 'forbid00': forbid, 'side': side, 'impose_phase': impose_phase,
            'initial_entries': init, 'final_entries': fin, 'empty_sites': empty,
            'root_alive': root in lists[(c, c)], 'revisions': revs}, lists

def sigma_patch(outer, levels):
    # children under phi', as in the substitution table of Appendix A
    def kids(l):
        T, K, B, X, Y = l
        kN, kS, kE, kW = thick_edges(K)
        tN, tS, tE, tW = THIN[T]
        s = {'a': 'b', 'b': 'b', 'c': 'c', 'd': 'c', 'e': 'c'}[B]
        n = {'a': 'e', 'b': 'd', 'c': 'd', 'd': 'd', 'e': 'e'}[B]
        SW = ('a', K, B, 1 - X, 1 - Y)
        SE = ('c', ('L', tS, kE), s, 0, 1 - Y)
        NW = ('d', ('L', kN, tW), n, 1 - X, 0)
        NE = ('b', ('C', F(T)), 'a', 0, 0)
        return SW, SE, NW, NE
    grid = {(0, 0): outer}
    n = 1
    for _ in range(levels):
        g2 = {}
        for (x, y), l in grid.items():
            SW, SE, NW, NE = kids(l)
            g2[(2 * x, 2 * y)] = SW; g2[(2 * x + 1, 2 * y)] = SE
            g2[(2 * x, 2 * y + 1)] = NW; g2[(2 * x + 1, 2 * y + 1)] = NE
        grid = g2; n *= 2
    for (x, y), l in grid.items():
        assert l in LET, ('illegal child', l)
        if (x + 1, y) in grid: assert edge(l, 'E') == edge(grid[(x + 1, y)], 'W')
        if (x, y + 1) in grid: assert edge(l, 'N') == edge(grid[(x, y + 1)], 'S')
    return grid, n

out = {'engine': 'C', 'guard': GUARD, 'cases': []}
t0 = time.monotonic()
outer = {'a': ('d', ('L', 'G0', 'G1'), 'd', 0, 0), 'b': ('a', ('C', 'a'), 'a', 0, 0),
         'c': ('c', ('L', 'G0', 'G1'), 'b', 0, 0), 'd': ('b', ('C', 'a'), 'a', 0, 0)}
for k in 'abcd':
    for forbid in (False, True):
        r, lists = corner_case(k, forbid)
        if not forbid:
            g, n = sigma_patch(outer[k], 6)
            assert n == 64
            assert g[(32, 32)] == ('a', ('C', k), 'a', 1, 1)
            lost = sum(1 for x in range(33) for y in range(33)
                       if LET.index(g[(x + 16, y + 16)]) not in lists[(x, y)])
            r['control_word_cells_lost'] = lost
        print(json.dumps(r), flush=True)
        out['cases'].append(r)
# Robustness: do NOT impose the thin phase (AC must derive it itself).
for k in 'abcd':
    r, _ = corner_case(k, True, impose_phase=False)
    print(json.dumps(r), flush=True)
    out['cases'].append(r)
# Informational: smallest odd box side that still empties (root at centre).
minimal = {}
for k in 'abcd':
    for side in range(3, 34, 2):
        r, _ = corner_case(k, True, side=side)
        if not r['root_alive']:
            minimal[k] = side
            break
print(json.dumps({'minimal_emptying_side': minimal}), flush=True)
out['minimal_emptying_side'] = minimal
out['elapsed'] = time.monotonic() - t0
with open(os.path.join(HERE, 'ENGINE-C.results.json'), 'w') as f:
    json.dump(out, f, indent=1)
print('DONE', len(out['cases']), round(out['elapsed'], 2), flush=True)
