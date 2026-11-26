#!/usr/bin/env python3
"""Exact finite checks of the two constructions; the proof covers all sizes."""

from itertools import product
from math import gcd, lcm


def test_radix():
    coefficients = [
        (1, 1), (1, 2), (-2, -1), (-1, -1), (2, -3),
        (6, 2, -3), (3, -2, 2), (4, -6, 2), (2, 4, -2, 4),
        (-2, 2, -2, 2, -2), (1, -1, 1, -1, 1),
    ]
    count = 0
    for original in coefficients:
        c = sorted(original, key=abs)
        u, v, arity = abs(c[0]), abs(c[-1]), len(c)
        L = lcm(*c)
        for mult in (1, 2):
            r = L * mult
            if r < 2 or r * u < v:
                continue
            steps = [u * r**i // abs(x) for i, x in enumerate(c)]
            assert all(abs(x) * step == u * r**i
                       for i, (x, step) in enumerate(zip(c, steps)))
            sets = [tuple(1 + step*j for j in range(r)) for step in steps]
            assert all(len(A) == r and min(A) >= 1
                       and (max(A)-1)*v <= u*r**arity for A in sets)
            values = {sum(x*y for x, y in zip(c, point)) for point in product(*sets)}
            assert len(values) == r**arity
            assert values == set(range(min(values), max(values)+1, u))
            count += 1
    return count


def subsets(mask):
    return [i for i in range(mask+1) if i & ~mask == 0]


def test_bilinear():
    count = 0
    for u, v in ((1, 1), (1, 2), (2, 1), (2, 3), (3, 5), (4, 3)):
        assert gcd(u, v) == 1
        for J in (1, 2, 3):
            high = 1 << J
            for D in range(high):
                U, V = subsets(D), subsets((high-1) ^ D)
                q = lcm(v*len(U), u*len(V))
                a, b = q // (v*len(U)), q // (u*len(V))
                A = {d + v*(i+a*b*x)
                     for d, i, x in product(range(v), range(a), U)}
                B = {e + u*(a*j+a*b*y)
                     for e, j, y in product(range(u), range(b), V)}
                assert len(A) == len(B) == q
                assert min(A) == min(B) == 0
                assert max(A) == v-1+v*(a-1+a*b*D)
                assert max(B) == u-1+u*(a*(b-1)+a*b*(high-1-D))
                for s, t in ((u, v), (-u, v), (-u, -v)):
                    assert len({s*x+t*y for x in A for y in B}) == q*q
                count += 1
    return count


if __name__ == "__main__":
    print(f"Verified {test_radix()} unrestricted positional systems and "
          f"{test_bilinear()} bilinear balancing fixtures.")
