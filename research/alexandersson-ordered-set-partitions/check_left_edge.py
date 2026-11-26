"""Certify the three most negative real zeros and their order in adjacent rows."""

from fractions import Fraction

from check_edge import ordered_rows, value_sign, variations_above


def largest_positive_brackets(poly, count):
    # Eneström–Kakeya on O_n bounds the magnitudes of the zeros of O_n(-y).
    top = 1 + max((abs(a) + abs(b) - 1) // abs(b) for a, b in zip(poly, poly[1:]))
    high = Fraction(top)
    high_sign = value_sign(poly, high)
    assert high_sign != 0
    brackets = []
    while len(brackets) < count:
        low = high * Fraction(10, 11)
        low_sign = value_sign(poly, low)
        assert low_sign != 0
        if low_sign != high_sign:
            left, right = low, high
            for _ in range(18):
                mid = (left + right) / 2
                sign = value_sign(poly, mid)
                if sign == low_sign:
                    left = mid
                elif sign == high_sign:
                    right = mid
                else:
                    left = right = mid
                    break
            brackets.append((left, right))
        high, high_sign = low, low_sign
        assert high > Fraction(1, 10**8)
    # Disjoint sign changes give the lower bound. Descartes counts multiplicity.
    assert variations_above(poly, high) == count
    return brackets


def certify(j, m, rows):
    brackets = []
    for n in range(j * m, j * (m + 1) + 1):
        reflected = [a * (-1)**k for k, a in enumerate(rows[n])]
        brackets.append(largest_positive_brackets(reflected, 3))
    for s, (old, new) in enumerate(zip(brackets, brackets[1:])):
        earlier, later = (old, new) if s < j - 1 else (new, old)
        assert all(a[0] > b[1] for a, b in zip(earlier, later))
        assert all(b[0] > a[1] for b, a in zip(later, earlier[1:]))
    return 3 * len(brackets)


if __name__ == '__main__':
    total = 0
    for threshold in (2, 3, 5, 8):
        rows = ordered_rows(threshold * 25, threshold)
        for quotient in (12, 24):
            total += certify(threshold, quotient, rows)
    print(f'{total} most-negative real zeros certified across 8 complete residue cycles')
