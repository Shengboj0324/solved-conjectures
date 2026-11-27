"""Certify the first three real roots of neighboring rows with integer arithmetic."""

from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb, factorial, pi


def ordered_rows(max_n, threshold):
    rows = [[1]]
    for n in range(1, max_n + 1):
        row = [0] * (1 + n // threshold)
        for size in range(1, n + 1):
            weight = comb(n, size)
            shift = int(size >= threshold)
            for k, coefficient in enumerate(rows[n - size]):
                row[k + shift] += weight * coefficient
        rows.append(row)
    return rows


def critical_estimate(j):
    # These approximations only select rational test points. All signs below are exact.
    with localcontext() as ctx:
        ctx.prec = 55

        def partial(x, k):
            return sum(x**i / factorial(i) for i in range(k + 1))

        def B(x):
            return (2 - x ** (j - 1) / factorial(j - 1)) * x.exp() - 2 * partial(x, j - 2)

        low, high = Decimal('0.65'), Decimal(2)
        for _ in range(130):
            mid = (low + high) / 2
            if B(mid) > 0:
                low = mid
            else:
                high = mid
        r = (low + high) / 2
        tail = r.exp() - partial(r, j - 1)
        tc = (2 - partial(r, j - 1)) / tail
        deriv = (2 - r ** (j - 1) / factorial(j - 1) - r ** (j - 2) / factorial(j - 2)) * r.exp()
        if j >= 3:
            deriv -= 2 * partial(r, j - 3)
        curvature = -deriv / tail**2
        return float(tc), float(r * r * curvature / 2) * pi**2


def value_sign(poly, x):
    p, q = x.as_integer_ratio()
    value, factor = poly[-1], 1
    for coefficient in reversed(poly[:-1]):
        factor *= q
        value = value * p + coefficient * factor
    return (value > 0) - (value < 0)


def variations_above(poly, x):
    # Descartes' rule on q^d P((y+p)/q), with x=p/q.
    p, q = x.as_integer_ratio()
    d = len(poly) - 1
    scaled = [a * q ** (d - k) for k, a in enumerate(poly)]
    shifted = [sum(comb(k, i) * scaled[k] * p ** (k - i) for k in range(i, d + 1))
               for i in range(d + 1)]
    signs = [a > 0 for a in shifted if a]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def isolate(poly, n, tc, spacing):
    endpoints = [Fraction(round((tc - spacing * (k + 0.5)**2 / n**2) * 10**8), 10**8)
                 for k in range(4)]
    assert variations_above(poly, endpoints[-1]) == 3
    assert [value_sign(poly, x) for x in endpoints] == [1, -1, 1, -1]
    intervals = []
    for idx, (high, low) in enumerate(zip(endpoints, endpoints[1:])):
        high_sign = (-1)**idx
        for _ in range(22):
            mid = (low + high) / 2
            sign = value_sign(poly, mid)
            if sign == high_sign:
                high = mid
            elif sign == -high_sign:
                low = mid
            else:
                low = high = mid
                break
        intervals.append((low, high))
    return intervals


if __name__ == '__main__':
    for j in (2, 3, 5, 8):
        tc, spacing = critical_estimate(j)
        rows = ordered_rows(193, j)
        for n in (96, 192):
            current = isolate(rows[n], n, tc, spacing)
            following = isolate(rows[n + 1], n + 1, tc, spacing)
            assert all(old[1] < new[0] for old, new in zip(current, following))
            assert all(new[1] < old[0] for old, new in zip(current, following[1:]))
        print(f'j={j}: first three real zeros certified and ordered at n=96,97,192,193')
