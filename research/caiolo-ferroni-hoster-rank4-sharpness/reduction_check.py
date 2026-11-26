#!/usr/bin/env python3
"""Rank-4 reduction for CFH dual Chow polynomials (exact, SymPy).

Rank 4 (R = {1,2,3}), CFH Theorem 4.9:
  H* = a(1+x)^3 + b x(1+x)
  F* = a(1+x)^4 + c x(1+x)^2 + d x^2
with a = beta(123), b = beta(13)+beta(23), e = beta(12), c = b+e, d = beta(2).

Claims checked here:
  (1) H* always has 3 real negative roots when a>0, b>=0.
  (2) F* real-rooted  <=>  (e+b)^2 >= 4ad.
  (3) H* interlaces F* <=> ad <= e*b   (and (3) implies (2)).
"""
import itertools, random
import sympy as sp

x, z = sp.symbols('x z')
a, b, e, d = sp.symbols('a b e d', positive=True)
c = b + e
H = a*(1+x)**3 + b*x*(1+x)
F = a*(1+x)**4 + c*x*(1+x)**2 + d*x**2

# Expand the gamma vectors exactly as CFH Thm 4.9 prescribes for r=4.
def thm49(beta, augmented):
    R = (1, 2, 3); r = 4
    tot = 0
    for k in range(len(R)+1):
        for S in itertools.combinations(R, k):
            if any(j-i == 1 for i, j in zip(S, S[1:])): continue
            if not augmented and (r-1) in S: continue
            Sc = tuple(i for i in R if i not in S)
            n = (r if augmented else r-1) - 2*len(S)
            tot += beta[Sc] * x**len(S) * (1+x)**n
    return sp.expand(tot)

B = {S: sp.Symbol('b'+''.join(map(str, S))) for k in range(4) for S in itertools.combinations((1,2,3), k)}
sub = {a: B[(1,2,3)], b: B[(1,3)]+B[(2,3)], e: B[(1,2)], d: B[(2,)]}
assert sp.expand(H.subs(sub) - thm49(B, False)) == 0
assert sp.expand(F.subs(sub) - thm49(B, True)) == 0
print('Thm 4.9 specialisation to rank 4: OK')

# p(z) = a + c z + d z^2 with F*/(1+x)^4 = p(x/(1+x)^2).
p = a + c*z + d*z**2
assert sp.simplify(F/(1+x)**4 - p.subs(z, x/(1+x)**2)) == 0
# value of p at the root z0=-a/b of H*/(1+x)
val = sp.factor(p.subs(z, -a/b))
assert sp.simplify(val - a*(a*d - e*b)/b**2) == 0
print('p(-a/b) = a(ad - be)/b^2: OK')

def real_roots(poly):
    return sorted(float(r) for r in sp.Poly(poly, x).real_roots())

def interlaces(f, g):
    """f (deg n-1) interlaces g (deg n): g1<=f1<=g2<=...<=f_{n-1}<=g_n"""
    rf, rg = real_roots(f), real_roots(g)
    if len(rg) != sp.degree(g, x) or len(rf) != sp.degree(f, x): return False
    return all(rg[i] <= rf[i] + 1e-12 and rf[i] <= rg[i+1] + 1e-12 for i in range(len(rf)))

random.seed(1)
n_rr = n_il = 0
for trial in range(3000):
    vals = {a: random.randint(1, 30), b: random.randint(1, 30), e: random.randint(0, 30), d: random.randint(0, 60)}
    Hn, Fn = H.subs(vals), F.subs(vals)
    A, Bv, E, Dv = (vals[s] for s in (a, b, e, d))
    assert len(real_roots(Hn)) == 3 and max(real_roots(Hn)) < 0
    rr = len(real_roots(Fn)) == 4 if Dv else True
    assert rr == ((E+Bv)**2 >= 4*A*Dv), vals
    if Dv:
        assert interlaces(Hn, Fn) == (A*Dv <= E*Bv), vals
    n_rr += rr; n_il += (A*Dv <= E*Bv)
print(f'random exact checks OK ({n_rr} real-rooted, {n_il} interlacing of 3000)')
