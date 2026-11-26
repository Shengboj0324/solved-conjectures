#!/usr/bin/env python3
"""Check the line-level form of the rank-4 slack (NOTES.md, section 4):
  E*B - X*A = -K + sum_l t_l (s_l - n) + (E+X)*Pi - (2E+X)*f3 - (n-1)*E
with K = f2*sum_l (s_l-1) t_l - (sum_l (s_l-1))(sum_l t_l), Pi = sum_P p_P,
s_l = points on line l, t_l = planes containing l."""
import numpy as np
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
from pg_fast import PG3
from flags4 import betas_from_alpha
for q in (3, 5, 7):
    g = PG3(q); rng = np.random.default_rng(q)
    for _ in range(60):
        S = rng.random(g.v) < rng.uniform(0.05, 0.9)
        if S.sum() < 5 or not g.spans(S): continue
        be = betas_from_alpha(g.alpha(S))
        E, X, A, B = be[(1,2)], be[(2,)], be[(1,2,3)], be[(1,3)] + be[(2,3)]
        s = S[g.line_pts].sum(1); ok = s >= 2
        Lp = np.zeros(g.v, int); np.add.at(Lp, g.line_planes[ok].ravel(), 1)
        r3 = Lp >= 2
        t = r3[g.line_planes].sum(1)          # rank-3 planes through each line
        sl, tl = s[ok].astype(object), t[ok].astype(object)
        n = int(S.sum()); f2 = int(ok.sum()); f3 = int(r3.sum())
        Pi = int(S[g.plane_pts].sum(1)[r3].sum())
        K = f2 * sum((sl - 1) * tl) - sum(sl - 1) * sum(tl)
        rhs = -K + sum(tl * (sl - n)) + (E + X) * Pi - (2 * E + X) * f3 - (n - 1) * E
        assert E * B - X * A == rhs
print('covariance identity verified on random subsets of PG(3,3), PG(3,5), PG(3,7)')
