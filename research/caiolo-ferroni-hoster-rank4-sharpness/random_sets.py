#!/usr/bin/env python3
"""R2 for random point sets of size ~ c q^2 in PG(3,q): tests the claim R2 -> 1."""
import sys, numpy as np, time
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
from pg_fast import PG3
from flags4 import betas_from_alpha, ratios
import pg_search as G

# cross-check fast engine against the slow one at q=3,5
for q in (3, 5):
    g, slow = PG3(q), G.pg(q)
    rng = np.random.default_rng(q)
    for _ in range(40):
        S = rng.random(g.v) < rng.uniform(0.1, 0.9)
        # slow engine uses its own point order; map by coordinates
        idx = {tuple(p): i for i, p in enumerate(slow[0])}
        Sslow = [idx[tuple(int(x) for x in g.P[i])] for i in np.nonzero(S)[0]]
        if not g.spans(S): continue
        assert g.alpha(S) == G.flags(Sslow, slow), q
print('fast engine agrees with slow engine', flush=True)

rng = np.random.default_rng(0)
for q in [int(a) for a in sys.argv[1:]] or [7, 11, 13, 17]:
    t = time.time(); g = PG3(q)
    row = []
    for c in (1.0, 1.5, 2.0, 2.5, 3.0, 4.0, 6.0):
        best = 0
        for _ in range(3):
            S = rng.random(g.v) < c / q
            if not g.spans(S): continue
            R1, R2 = ratios(betas_from_alpha(g.alpha(S)))
            best = max(best, float(R2))
        row.append(f'c={c}:{best:.4f}')
    print(f'q={q:3d} ({time.time()-t:.0f}s)  ' + '  '.join(row), flush=True)
