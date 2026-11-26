"""Exact flag numbers of rank-4 geometric lattices and the two CFH rank-4 ratios.

A rank-4 simple matroid is given by its atoms (points), lines and planes (hyperplanes),
each line/plane a frozenset of points.  alpha(S) = number of chains of flats with rank set S.
R2 = beta123*beta2 / (beta12*(beta13+beta23))      interlacing fails iff R2 > 1
R1 = 4*beta123*beta2 / (beta12+beta13+beta23)^2     F* real-rootedness fails iff R1 > 1
"""
from fractions import Fraction
from itertools import combinations


def betas_from_alpha(al):
    R = (1, 2, 3)
    subs = [S for k in range(4) for S in combinations(R, k)]
    return {S: sum((-1) ** (len(S) - len(T)) * al[T] for T in subs if set(T) <= set(S)) for S in subs}


def alpha_from_flats(npts, lines, planes):
    lines = [frozenset(l) for l in lines]
    al = {(): 1, (1,): npts, (2,): len(lines), (3,): len(planes)}
    al[(1, 2)] = sum(len(l) for l in lines)
    al[(1, 3)] = sum(len(P) for P in planes)
    a23 = a123 = 0
    for P in planes:
        P = frozenset(P)
        for l in lines:
            if l <= P:
                a23 += 1; a123 += len(l)
    al[(2, 3)] = a23; al[(1, 2, 3)] = a123
    return al


def ratios(be):
    a, d, e, b = be[(1, 2, 3)], be[(2,)], be[(1, 2)], be[(1, 3)] + be[(2, 3)]
    R2 = Fraction(a * d, e * b) if e * b else float('inf')
    R1 = Fraction(4 * a * d, (e + b) ** 2)
    return R1, R2


def report(name, al):
    be = betas_from_alpha(al)
    assert all(v >= 0 for v in be.values()), (name, be)
    R1, R2 = ratios(be)
    return name, float(R1), float(R2), be
