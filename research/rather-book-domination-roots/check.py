"""Regression only. README.md proves the classifications uniformly."""
from collections import Counter
from fractions import Fraction
from math import comb
import sympy as sp

def formula(n):
    out = Counter()
    for j in range(n + 1):
        v = comb(n, j) * 2**(n - j)
        out[n + j] += v
        out[n + j + 1] += 2 * v
    for j in range(2 * n + 1):
        out[j + 2] += comb(2 * n, j)
    out[n] -= 2
    return +out

def direct(n):
    m = 2 * n + 2
    nb = [(1 << u) for u in range(m)]
    edges = [(0, 1)]
    for i in range(n):
        u, v = 2 + 2*i, 3 + 2*i
        edges += [(1, u), (u, v), (v, 0)]
    for u, v in edges:
        nb[u] |= 1 << v
        nb[v] |= 1 << u
    covers = [0] * (1 << m)
    result = Counter()
    for s in range(1, 1 << m):
        bit = s & -s
        covers[s] = covers[s - bit] | nb[bit.bit_length() - 1]
        if covers[s] == (1 << m) - 1:
            result[s.bit_count()] += 1
    return result

for n in range(1, 8):
    assert direct(n) == formula(n)
x = sp.Symbol("x")
for n in range(1, 49):
    p = sp.Poly.from_dict({(k - 2,):v for k,v in formula(n).items()},x)
    assert p.eval(0) > 0 and p.eval(-2) != 0 and p.eval(sp.Rational(-1,2)) != 0
    intervals = p.intervals(eps=sp.Rational(1,10**6))
    assert sum(m for (lo,hi),m in intervals) == (0 if n == 1 else 2), (n,intervals)
    assert all(m == 1 for _,m in intervals)
    expected = (0,0) if n==1 else ((1,1) if n%2==0 else (0,2))
    found = (sum(int(bool(hi <= -2)) for (lo,hi),_ in intervals),
             sum(int(bool(lo >= sp.Rational(-1,2) and hi <= 0)) for (lo,hi),_ in intervals))
    assert found == expected,(n,intervals)
assert (1-2*Fraction(1,5))*(2-Fraction(1,5))**3 - (1-Fraction(1,5))**6/Fraction(1,5) - 2 == Fraction(589,3125)
assert Fraction(4,5)**5/3 + 6*Fraction(3,5)**5 < 1
print("Direct enumeration through seven pages; exact rational real-root isolation through 48 pages; exact sign constants passed.")
