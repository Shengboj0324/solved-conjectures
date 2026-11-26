"""Compare direct hull and chain counts with the binary split formulas."""

from fractions import Fraction
from itertools import combinations
from math import comb, factorial


def cross(a, b, c):
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def hull(points):
    stack = []
    for p in points:
        while len(stack) >= 2 and cross(stack[-2], stack[-1], p) <= 0:
            stack.pop()
        stack.append(p)
    return stack


def counts(points):
    n = len(points)
    cups, caps, convex = ([0] * (n + 1) for _ in range(3))
    for k in range(1, n + 1):
        for subset in combinations(points, k):
            turns = [cross(*triple) for triple in zip(subset, subset[1:], subset[2:])]
            cups[k] += all(t > 0 for t in turns)
            caps[k] += all(t < 0 for t in turns)
            vertices = set(hull(subset)) | set(hull(reversed(subset)))
            convex[k] += len(vertices) == k
    return cups, caps, convex


def test_finite():
    points = [(0, 0)]
    u, f = [0, 1], [0, 1]
    totals = 0
    for depth in range(4):
        n = len(points)
        points += [(x + 4**depth, y + 16**depth) for x, y in points]
        assert all(cross(*triple) for triple in combinations(points, 3))
        new_u, new_f = [0] * (2 * n + 1), [0] * (2 * n + 1)
        for k in range(1, n + 1):
            new_u[k] += 2 * u[k]
            new_u[k + 1] += n * u[k]
            new_f[k] += 2 * f[k]
            for j in range(1, n + 1):
                new_f[k + j] += u[k] * u[j]
        u, f = new_u, new_f
        observed = counts(points)
        assert observed == (u, u, f)
        totals += sum(comb(2 * n, k) for k in range(1, 2 * n + 1))
    return totals


def test_limit():
    u = [Fraction(1), Fraction(1)]
    q = [Fraction(1)]
    p = [Fraction(1), Fraction(1)]
    for k in range(2, 45):
        u.append(u[-1] * Fraction(k, 2**k - 2))
        q.append(q[-1] * (1 - Fraction(1, 2**(k-1))))
        exact = sum(comb(k, j) * u[j] * u[k-j] for j in range(1, k)) / (2**k - 2)
        p.append(exact)
        # Recover the same probabilities by conditioning on the first bit
        # that separates the sample and using the product formula for its cups.
        total = 0
        for j in range(1, k):
            other = k - j
            power = j * (j + 1) // 2 + other * (other + 1) // 2
            term = Fraction(4 * factorial(k), 2**power)
            total += term / (q[j - 1] * q[other - 1])
        assert total / (2**k - 2) == exact
    assert p[3:5] == [1, Fraction(5, 7)]
    return len(p) - 2


if __name__ == "__main__":
    print(f"{test_finite()} nonempty planar subsets; {test_limit()} exact limit coefficients")
