"""Check the leading coefficients and strict long-row interlacing exactly."""

from math import comb, factorial

import sympy as sp

from natural_descent import numerator


def disjoint_negative_roots(coefficients):
    x = sp.Symbol('x')
    p = sp.Poly.from_list(coefficients[::-1], x)
    intervals = p.intervals(eps=sp.Rational(1, 10**16))
    assert len(intervals) == p.degree()
    assert all(high < 0 and multiplicity == 1 for (low, high), multiplicity in intervals)
    return [interval for interval, _ in intervals]


if __name__ == '__main__':
    checked_coefficients = checked_zeros = 0
    for tail in ((2, 1), (3, 2, 1), (3, 3, 3), (4, 2, 1), (2, 2, 1, 1), (4, 3, 1)):
        h = numerator(tail)
        p = sum(tail)
        first = tail[0] + p
        rows = [numerator((m,) + tail) for m in range(first, first + p + 1)]
        limit = []
        for k in range(p + 1):
            expected = sum(h[d] * comb(p - d, k - d) for d in range(min(k, len(h)-1) + 1))
            difference = sum((-1)**(k-i) * comb(k, i) * rows[i][k] for i in range(k+1))
            assert difference == expected
            limit.append(sp.Rational(expected, factorial(k)))
            checked_coefficients += 1
        assert len(disjoint_negative_roots(limit)) == p
        old = disjoint_negative_roots(numerator((48,) + tail))
        new = disjoint_negative_roots(numerator((49,) + tail))
        assert len(old) == len(new) == p
        assert all(a[1] < b[0] for a, b in zip(old, new))
        assert all(b[1] < a[0] for b, a in zip(new, old[1:]))
        checked_zeros += len(old) + len(new)
    print(f'{checked_coefficients} exact leading coefficients and {checked_zeros} finite-row roots checked')
