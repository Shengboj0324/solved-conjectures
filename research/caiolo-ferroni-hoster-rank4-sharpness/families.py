#!/usr/bin/env python3
"""Closed-form / symbolic families of rank-4 matroids."""
import sympy as sp
from math import comb
from functools import lru_cache
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
from flags4 import betas_from_alpha, ratios

q, n, t = sp.symbols('q n t', positive=True)

def gauss(d, i, Q=q):
    if i < 0 or i > d: return 0
    num = den = sp.Integer(1)
    for j in range(i):
        num *= Q**(d-j) - 1; den *= Q**(j+1) - 1
    return sp.cancel(num/den)

def show(name, al):
    be = betas_from_alpha(al)
    a, d, e, b = (sp.expand(v) for v in (be[(1,2,3)], be[(2,)], be[(1,2)], be[(1,3)]+be[(2,3)]))
    v = list((a*d).free_symbols)[0]
    R2 = sp.limit(a*d/(e*b), v, sp.oo)
    print(f'{name:38s} interlace slack e*b-a*d = {sp.factor(e*b-a*d)}')
    print(f'{"":38s} lim R2 = {R2}')

# 1. Uniform U_{4,n}
al = {(): 1, (1,): n, (2,): n*(n-1)/2, (3,): n*(n-1)*(n-2)/6}
al[(1,2)] = 2*al[(2,)]; al[(1,3)] = 3*al[(3,)]; al[(2,3)] = 3*al[(3,)]; al[(1,2,3)] = 6*al[(3,)]
show('U(4,n)', {k: sp.expand(v) for k, v in al.items()})

# 2. PG(3,q)
pts, lns, pls = gauss(4,1), gauss(4,2), gauss(4,3)
al = {(): 1, (1,): pts, (2,): lns, (3,): pls, (1,2): lns*(q+1), (1,3): pls*(q*q+q+1),
      (2,3): pls*(q*q+q+1), (1,2,3): pls*(q*q+q+1)*(q+1)}
show('PG(3,q)', {k: sp.expand(sp.cancel(v)) for k, v in al.items()})

# 3. AG(3,q) (affine space)
pts = q**3; lns = q**2*(q*q+q+1); pls = q*(q*q+q+1)
al = {(): 1, (1,): pts, (2,): lns, (3,): pls, (1,2): lns*q, (1,3): pls*q*q,
      (2,3): pls*q*(q+1), (1,2,3): pls*q*(q+1)*q}
show('AG(3,q)', {k: sp.expand(v) for k, v in al.items()})

# 4. Rank-4 coalescence (BCEL / repo construction with k=3): V=F_q^6, m=q^3 free points, b=q^9 blocks
k = 3; m = q**3; bb = q**9
@lru_cache(None)
def A(dd, tt, S):
    if not S: return sp.Integer(1)
    s = S[-1]
    return sp.expand(sum(gauss(dd, i)*sp.binomial(tt, s-i)*A(i, s-i, S[:-1]) for i in range(max(0, s-tt) if isinstance(tt,int) else 0, min(dd, s)+1)))
def choose_m(j):
    o = sp.Integer(1)
    for i in range(j): o *= (m - i)
    return o/sp.factorial(j)
def Abin(dd, tt_is_m, S):
    # product of subspaces of F_q^dd and the Boolean lattice on m points
    if not S: return sp.Integer(1)
    s = S[-1]
    return sum(gauss(dd, i)*choose_m(s-i)*A(i, s-i, S[:-1]) for i in range(0, min(dd, s)+1))
def alpha(S):
    if not S: return sp.Integer(1)
    s, T = S[-1], S[:-1]
    v = Abin(2*k, True, S)
    if s == k:
        v += bb*(A(k, 1, T) - A(k, 0, T) - gauss(k, k-1)*A(k-1, 1, T))
    return sp.expand(sp.cancel(v))
from itertools import combinations
al = {S: alpha(S) for j in range(4) for S in combinations((1,2,3), j)}
show('coalescence rank 4 (k=3)', al)
# numeric R2 at small q
be = betas_from_alpha(al)
for qq in (2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,64,128,1024):
    vals = {S: int(v.subs(q, qq)) for S, v in be.items()}
    R1, R2 = ratios(vals)
    print(f'   q={qq:5d}  R1={float(R1):.5f}  R2={float(R2):.5f}')
