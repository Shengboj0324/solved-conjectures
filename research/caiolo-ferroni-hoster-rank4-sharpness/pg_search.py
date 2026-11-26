#!/usr/bin/env python3
"""Search simple rank-4 matroids represented by point sets S in PG(3,q), q prime.

Every simple F_q-representable rank-4 matroid is such an S.  For each S we compute the
exact flag numbers and R2 = b123*b2/(b12*(b13+b23)) (interlacing fails iff R2>1).
q=2: exhaustive over all 2^15 subsets.  q>2: random restarts + hill climbing on R2.
Usage: pg_search.py q [restarts] [steps] [seed]
"""
import sys, random
from itertools import product, combinations
from fractions import Fraction
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
from flags4 import betas_from_alpha, ratios


def pg(q):
    pts = []
    for v in product(range(q), repeat=4):
        if any(v):
            lead = next(x for x in v if x)
            inv = pow(lead, q - 2, q)
            w = tuple(x * inv % q for x in v)
            if w not in pts: pts.append(w)
    idx = {p: i for i, p in enumerate(pts)}
    def norm(v):
        lead = next(x for x in v if x); inv = pow(lead, q - 2, q)
        return idx[tuple(x * inv % q for x in v)]
    lines = set()
    for i, j in combinations(range(len(pts)), 2):
        u, w = pts[i], pts[j]
        L = frozenset({i, j} | {norm(tuple((u[k] + c * w[k]) % q for k in range(4))) for c in range(1, q)})
        lines.add(L)
    planes = []
    for h in pts:  # dual points = planes
        planes.append(frozenset(i for i, p in enumerate(pts) if sum(a * b for a, b in zip(h, p)) % q == 0))
    lines = list(lines)
    plane_lines = [[li for li, L in enumerate(lines) if L <= P] for P in planes]
    pt_lines = [[li for li, L in enumerate(lines) if i in L] for i in range(len(pts))]
    return pts, lines, planes, plane_lines


def flags(S, geo):
    pts, lines, planes, plane_lines = geo
    S = set(S)
    ls = [len(L & S) for L in lines]
    al = {(): 1, (1,): len(S)}
    f2 = a12 = f3 = a13 = a23 = a123 = 0
    for c in ls:
        if c >= 2: f2 += 1; a12 += c
    for P, pl in zip(planes, plane_lines):
        PS = P & S
        if len(PS) < 3: continue
        inner = [ls[li] for li in pl if ls[li] >= 2]
        # rank 3 iff PS is not contained in a single line: i.e. not (one line contains all of PS)
        if any(c == len(PS) for c in inner): continue
        f3 += 1; a13 += len(PS); a23 += len(inner); a123 += sum(inner)
    al.update({(2,): f2, (3,): f3, (1, 2): a12, (1, 3): a13, (2, 3): a23, (1, 2, 3): a123})
    return al


def spans(S, geo):
    # rank 4 iff some plane-free: S not contained in any plane
    return all(not set(S) <= P for P in geo[2])


def score(S, geo):
    if len(S) < 4 or not spans(S, geo): return None
    be = betas_from_alpha(flags(S, geo))
    R1, R2 = ratios(be)
    return R2, R1, be


def main():
    q = int(sys.argv[1]); restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    steps = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
    random.seed(int(sys.argv[4]) if len(sys.argv) > 4 else 0)
    geo = pg(q); N = len(geo[0])
    print(f'PG(3,{q}): {N} points, {len(geo[1])} lines, {len(geo[2])} planes')
    best = (Fraction(0), None, None)
    if q == 2:
        for mask in range(1, 1 << N):
            S = [i for i in range(N) if mask >> i & 1]
            s = score(S, geo)
            if s and s[0] > best[0]: best = (s[0], S, s)
        print('exhaustive best R2 =', float(best[0]), 'S =', best[1], 'betas', best[2][2])
        return
    for r in range(restarts):
        S = set(random.sample(range(N), random.randint(5, N)))
        s = score(S, geo)
        while s is None:
            S = set(random.sample(range(N), random.randint(5, N))); s = score(S, geo)
        cur = s[0]
        for _ in range(steps):
            i = random.randrange(N)
            T = S ^ {i}
            t = score(T, geo)
            if t and t[0] >= cur:
                S, cur, s = T, t[0], t
        if cur > best[0]: best = (cur, sorted(S), s)
        print(f'restart {r}: R2={float(cur):.5f} |S|={len(S)}  best={float(best[0]):.5f}', flush=True)
    print('best R2 =', float(best[0]), '|S| =', len(best[1]), 'betas', best[2][2])
    print('S =', best[1])


if __name__ == '__main__':
    main()
