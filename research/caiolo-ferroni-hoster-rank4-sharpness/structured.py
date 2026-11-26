#!/usr/bin/env python3
"""Random background (c q^2 points) plus structured pieces, PG(3,q): does structure beat random?"""
import sys, numpy as np
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
from pg_fast import PG3
from flags4 import betas_from_alpha, ratios
q = int(sys.argv[1]) if len(sys.argv) > 1 else 13
g = PG3(q); rng = np.random.default_rng(7)
R = lambda S: float(ratios(betas_from_alpha(g.alpha(S)))[1]) if g.spans(S) else None
base = rng.random(g.v) < 2.5 / q
print('random c=2.5            ', R(base))
for k in (1, 3, q, 3 * q):
    S = base.copy(); S[g.line_pts[rng.choice(g.L, k, replace=False)].ravel()] = True
    print(f'+{k:3d} full lines        ', R(S))
for k in (1, 2, 4):
    S = base.copy(); S[g.plane_pts[rng.choice(g.v, k, replace=False)].ravel()] = True
    print(f'+{k} full planes          ', R(S))
# background confined to a few planes
for k in (3, 5, 8, q):
    planes = g.plane_pts[rng.choice(g.v, k, replace=False)]
    S = np.zeros(g.v, bool)
    for P in planes: S[P[rng.random(len(P)) < 2.5 * q / len(P) * 1.0 / 1]] = True
    print(f'random inside {k:2d} planes ', R(S), int(S.sum()))
# book: k planes through a common line, random inside
spine = 0; pl = g.line_planes[spine]
for k in (3, 6, q + 1):
    S = np.zeros(g.v, bool)
    for P in g.plane_pts[pl[:k]]: S[P[rng.random(len(P)) < 0.3]] = True
    print(f'book {k:2d} pages (30%)    ', R(S), int(S.sum()))
