#!/usr/bin/env python3
"""Exact checks of the plane decomposition used in NOTES.md.

(*)  E*B - X*A = sum_P [ E*(p_P + L_P - 2) - X*|mu_P| ] - (n-1)*E
where X=beta2, E=beta12, A=beta123, B=beta13+beta23, and for each plane P:
p_P points, L_P lines, |mu_P| = sum_{l in P}(s_l - 1) - p_P + 1.

(P)  For rank-4 paving matroids (all lines have 2 points):
     E*B - X*A = (n-2)/2 * sum_P g(p_P) - (n-1)^2 (n-2)/2,
     g(p) = -p^2 + (2n+1)p - 3n + 1.
Checked on random subsets of PG(3,3) for (*), and on random paving matroids for (P).
"""
import random
from itertools import combinations
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
from flags4 import betas_from_alpha, alpha_from_flats
import pg_search as G


def EXAB(be):
    return be[(1,2)], be[(2,)], be[(1,2,3)], be[(1,3)] + be[(2,3)]


def plane_data(S, geo):
    pts, lines, planes, plane_lines = geo
    S = set(S); out = []
    ls = [len(L & S) for L in lines]
    for P, pl in zip(planes, plane_lines):
        PS = P & S
        inner = [ls[li] for li in pl if ls[li] >= 2]
        if len(PS) < 3 or any(c == len(PS) for c in inner): continue
        out.append((len(PS), len(inner), sum(c - 1 for c in inner) - len(PS) + 1))
    return out


random.seed(5)
geo = G.pg(3); N = len(geo[0]); cnt = 0
while cnt < 300:
    S = random.sample(range(N), random.randint(5, N))
    if not G.spans(S, geo): continue
    be = betas_from_alpha(G.flags(S, geo)); E, X, A, B = EXAB(be); n = len(S)
    rhs = sum(E*(p+L-2) - X*mu for p, L, mu in plane_data(S, geo)) - (n-1)*E
    assert E*B - X*A == rhs; cnt += 1
print('(*) identity: 300 random PG(3,3) matroids OK')


def random_paving(n, tries):
    """big planes = random subsets pairwise meeting in <=2 points; rest triples."""
    big = []
    for _ in range(tries):
        k = random.randint(4, max(4, n // 2))
        P = frozenset(random.sample(range(n), k))
        if all(len(P & Q) <= 2 for Q in big): big.append(P)
    covered = set()
    for P in big:
        covered |= {frozenset(T) for T in combinations(sorted(P), 3)}
    planes = big + [frozenset(T) for T in combinations(range(n), 3) if frozenset(T) not in covered]
    lines = [frozenset(T) for T in combinations(range(n), 2)]
    return lines, planes


for trial in range(200):
    n = random.randint(6, 16)
    lines, planes = random_paving(n, random.randint(0, 12))
    if len(planes) < 2: continue
    be = betas_from_alpha(alpha_from_flats(n, lines, planes)); E, X, A, B = EXAB(be)
    g = lambda p: -p*p + (2*n+1)*p - 3*n + 1
    lhs2 = (n-2) * sum(g(len(P)) for P in planes) - (n-1)**2 * (n-2)
    assert 2*(E*B - X*A) == lhs2, (n, len(planes))
    assert E*B - X*A > 0
print('(P) paving identity and positivity: 200 random paving matroids OK')
