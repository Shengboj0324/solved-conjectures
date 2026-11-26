"""Compare exact Eulerian minors with the fixed-offset leading term."""

from fractions import Fraction
from itertools import combinations
from math import exp, factorial, prod


def determinant(values):
    a = [row[:] for row in values]
    previous = 1
    for k in range(len(a) - 1):
        pivot = a[k][k]
        assert pivot > 0
        for i in range(k + 1, len(a)):
            for j in range(k + 1, len(a)):
                numerator = pivot * a[i][j] - a[i][k] * a[k][j]
                a[i][j], remainder = divmod(numerator, previous)
                assert remainder == 0
        previous = pivot
    return a[-1][-1]


def vandermonde(indices):
    return prod(b - a for a, b in combinations(indices, 2))


def entries(points):
    rows = {}
    for a, b in points:
        rows.setdefault(a, set()).add(b)
    largest = max(b for _, b in points)
    row = [1] * (largest + 1)
    output = {}
    for a in range(max(rows) + 1):
        if a:
            for b in range(1, largest + 1):
                row[b] = (b + 1) * row[b] + (a + 1) * row[b - 1]
        for b in rows.get(a, ()):
            output[a, b] = row[b]
    return output


def normalized(n, m, a, b, table):
    r = len(a)
    d = r * (r - 1) // 2
    raw = determinant([[table[n+i, m+j] for j in b] for i in a])
    value = Fraction(raw * table[n, m]**r,
                     prod(table[n+i, m] for i in a) * prod(table[n, m+j] for j in b))
    scale = Fraction(vandermonde(a) * vandermonde(b), prod(factorial(j) for j in range(r)))
    return value * (n + m + 2)**d / scale


if __name__ == '__main__':
    sizes = (40, 120, 400)
    patterns = [((-2, 1), (0, 3)), ((0, 1, 2), (0, 1, 2)),
                ((-1, 1, 3), (-2, 0, 2)), ((-2, 0, 1, 3), (-1, 0, 2, 4))]
    table = entries({(n+i, n+j) for n in sizes for a, b in patterns
                     for i in (*a, 0) for j in (*b, 0)})
    for a, b in patterns:
        d = len(a) * (len(a)-1) // 2
        values = [normalized(n, n, a, b, table) / 4**d for n in sizes]
        assert all(v > 0 for v in values)
        assert abs(values[-1] - 1) < Fraction(1, 10)
        print(a, b, [round(float(v), 6) for v in values])

    a, b = patterns[-1]
    d = len(a) * (len(a)-1) // 2
    for tilt in (-3, 1, 3):
        exponential = exp(tilt)
        mean = exponential / (exponential - 1) - 1 / tilt
        variance = 1 / tilt**2 - exponential / (exponential - 1)**2
        constant = 1 + mean * (1 - mean) / variance
        centers = []
        for total in (300, 900):
            column = round(total * mean) - 1
            centers.append((total - column - 2, column))
        table = entries({(n+i, m+j) for n, m in centers for i in (*a, 0) for j in (*b, 0)})
        values = [float(normalized(n, m, a, b, table)) / constant**d for n, m in centers]
        assert abs(values[-1]-1) < 0.05
        print('tilt', tilt, [round(v, 6) for v in values])
