"""Verify substitution by literal maximal-set enumeration on small graphs."""
from fractions import Fraction
from itertools import combinations

from check import graph, maximal_independent_sets


def blow(base, parts):
    ranges = []
    next_start = 0
    for local in parts:
        ranges.append(((1 << len(local)) - 1) << next_start)
        next_start += len(local)
    adj = [0] * next_start
    start = 0
    for i, local in enumerate(parts):
        external = 0
        for j, block in enumerate(ranges):
            if base[i] & (1 << j):
                external |= block
        for j, neighbors in enumerate(local):
            adj[start + j] = external | (neighbors << start)
        start += len(local)
    return adj


def complete_pairs(d):
    full = (1 << (2 * d)) - 1
    return [full ^ (3 << (i // 2 * 2)) for i in range(2 * d)]


def check_graphs():
    prev = graph(2, 1, (1, 1))
    assert min(S.bit_count() for S in maximal_independent_sets(prev)) == 2
    for m, r in [(2, 1), (3, 1), (3, 2)]:
        base = graph(m, r, (1,) * m)
        big = blow(base, [complete_pairs(2)] * (m * r) + [prev] * m)
        actual = maximal_independent_sets(big)
        assert len(big) == m * (4 + 4 * r)
        assert min(S.bit_count() for S in actual) >= (m - r) * 2
        # A transversal consisting of one representative per maximal local
        # independent set in each of r+1 chosen P4 fibers.
        local = next(
            (1 << i) | (1 << j) for i, j in combinations(range(4), 2)
            if all(((1 << i) | (1 << j)) & S for S in maximal_independent_sets(prev))
        )
        upper = sum(local << (4 * m * r + 4 * j) for j in range(r + 1))
        assert upper.bit_count() == 2 * (r + 1) and all(upper & S for S in actual)
        for ids in combinations(range(len(big)), 2 * (r + 1) - 1):
            T = sum(1 << i for i in ids)
            assert any(not T & S for S in actual)
        print(f"Substitution graph: n={len(big)}, maximal sets={len(actual)}, "
              f"minimum size={min(S.bit_count() for S in actual)}, tau={2*(r+1)}")


def check_recurrence():
    for c in (Fraction(1, 20), Fraction(1, 2), Fraction(19, 20)):
        eta = (1 - c) / 8
        L, D, i = (8 / eta).__ceil__(), 1, (8 / eta).__ceil__()
        for t in range(1, 51):
            a = eta / (t + 1) ** 2
            rho = Fraction(D, L)
            r = a // rho
            m = (r / a).__ceil__()
            assert 1 <= r < m and a / rho >= 2
            L, D, i = m * (L + 2 * r * D), (r + 1) * D, (m - r) * i
            assert Fraction(i, L) >= c and a * rho / 4 <= Fraction(D, L) <= 2 * a * rho
    print("150 exact recurrence steps preserve hollowness and the ratio bounds.")


if __name__ == "__main__":
    check_graphs()
    check_recurrence()
