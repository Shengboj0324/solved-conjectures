"""Check the mixed-degree cardinal-spline integral using rational arithmetic."""

from fractions import Fraction
from functools import cache
from itertools import combinations
from math import comb, factorial


@cache
def spline_piece(index, left):
    """Coefficients on (left, left + 1), in powers of (x - left)."""
    return tuple(
        Fraction(comb(index, power), factorial(index))
        * sum(
            (-1) ** shift * comb(index + 1, shift) * (left - shift) ** (index - power)
            for shift in range(left + 1)
        )
        for power in range(index + 1)
    )


def gram_entry(row, column):
    total = Fraction(0)
    for left in range(min(row, column) + 1):
        for i, a in enumerate(spline_piece(row, left)):
            for j, b in enumerate(spline_piece(column, left)):
                total += a * b / (i + j + 1)
    return factorial(row + column + 1) * total


def main():
    side = 12
    entries = [[1] * side for _ in range(side)]
    for i in range(1, side):
        for j in range(1, side):
            entries[i][j] = (j + 1) * entries[i - 1][j] + (i + 1) * entries[i][j - 1]
    for i in range(side):
        for j in range(side):
            assert gram_entry(i, j) == entries[i][j], (i, j)
    pairs = list(combinations(range(side), 2))
    for i, k in pairs:
        for j, ell in pairs:
            assert entries[i][j] * entries[k][ell] > entries[i][ell] * entries[k][j]
    for i in range(side):
        for j in range(side):
            mixed = sum((-1)**(i + j - a - b) * comb(i, a) * comb(j, b) * entries[a][b]
                        for a in range(i + 1) for b in range(j + 1))
            assert mixed >= 0 and (mixed > 0) == ((i == j == 0) or (i > 0 and j > 0))
    positive_pairs = list(combinations(range(1, side), 2))
    for i, k in positive_pairs:
        for j, ell in positive_pairs:
            assert (entries[i][j] - 1) * (entries[k][ell] - 1) > (entries[i][ell] - 1) * (entries[k][j] - 1)
    print(f'{side**2} mixed differences and {len(positive_pairs)**2} bordered three-by-three minors passed')
    print(f'{side**2} exact spline integrals and {len(pairs)**2} two-by-two determinants passed')


if __name__ == '__main__':
    main()
