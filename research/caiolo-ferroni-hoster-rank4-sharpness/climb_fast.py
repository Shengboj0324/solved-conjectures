#!/usr/bin/env python3
"""Hill climbing on R2 over point sets in PG(3,q) using the vectorised engine.
Usage: climb_fast.py q steps seed [c]   -> writes logs/climb_q<q>_s<seed>.npy (best set)"""
import sys, numpy as np, time
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
from pg_fast import PG3
from flags4 import betas_from_alpha, ratios
q, steps, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
c = float(sys.argv[4]) if len(sys.argv) > 4 else 2.5
rng = np.random.default_rng(seed); g = PG3(q)
S = rng.random(g.v) < c / q
def R(S):
    if S.sum() < 5 or not g.spans(S): return -1
    return ratios(betas_from_alpha(g.alpha(S)))[1]
cur = R(S); t0 = time.time()
for it in range(steps):
    T = S.copy()
    for i in rng.integers(0, g.v, size=rng.integers(1, 4)): T[i] = ~T[i]
    r = R(T)
    if r >= cur: S, cur = T, r
    if it % 2000 == 0:
        print(f'it={it} R2={float(cur):.5f} |S|={S.sum()} ({time.time()-t0:.0f}s)', flush=True)
        np.save(f'logs/climb_q{q}_s{seed}.npy', S)
np.save(f'logs/climb_q{q}_s{seed}.npy', S)
print('final', float(cur), int(S.sum()))
