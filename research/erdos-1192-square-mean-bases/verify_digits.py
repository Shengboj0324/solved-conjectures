"""Exact fixtures for the cyclic randomized digit construction.

Run with Python 3.10+. No third-party tools or numerical tolerances.
"""
from collections import Counter
from itertools import product
from math import factorial
from random import Random


def colours(r, p, m, rng):
    out = []
    words = list(product(range(p), repeat=m))
    for i in range(r):
        needed = 0
        positions = []
        for k in range(r * m):
            if k % r == i:
                positions.append((needed, None))
                needed += 1
            else:
                table = {word: rng.randrange(p)
                         for word in product(range(p), repeat=needed)}
                positions.append((needed, table))
        out.append({sum(p**k * (word[j] if tab is None else tab[word[:j]])
                        for k, (j, tab) in enumerate(positions))
                    for word in words})
    return out


def cyclic_counts(base, r, period):
    counts = Counter({0: 1})
    for _ in range(r):
        new = Counter()
        for n, c in counts.items():
            for a in base:
                new[(n + a) % period] += c
        counts = new
    return counts


def energy(counts):
    return sum(c * c for c in counts.values())


def verify(r, p, m, seed, do_union):
    sets = colours(r, p, m, Random(seed))
    M = p ** (r * m)
    assert all(len(A) == p ** m for A in sets)
    counts = Counter(sum(word) % M for word in product(*[sorted(A) for A in sets]))
    assert len(counts) == M and set(counts.values()) == {1}

    parts = []
    for i, A in enumerate(sets):
        e = energy(cyclic_counts(A, r, M))
        parts.append(e)
        shell_lb = 0
        for k in range(1, r * m + 1):
            projections = Counter(a % p**k for a in A)
            d = sum(j % r == i for j in range(k))
            assert len(projections) == p**d
            assert set(projections.values()) == {p**(m-d)}
            if (k - 1) % r != i:
                shift = k - 1 - r*d
                # Lower bound equals M*(p-1)*p**shift, an integer.
                shell_lb += (p - 1) * p ** (r * m + shift)
        assert e >= M + shell_lb  # zero-frequency term plus selected shells
    if do_union:
        B = set.union(*sets)
        e = energy(cyclic_counts(B, r, M))
        assert max(parts) <= e <= r ** (2*r-1) * sum(parts)
    return M, sum(parts)


def lifts():
    for r, p, m in [(2, 3, 2), (3, 5, 1), (4, 5, 1)]:
        sets = colours(r, p, m, Random(17))
        M = p**(r*m)
        D = 6*r
        shortest = {}
        for word in product(*sets):
            s = sum(word)
            shortest[s % M] = s
        for n in range(2*r*M, D*M):
            s = shortest[n % M]
            k, rem = divmod(n-s, M)
            assert rem == 0 and r <= k <= D
            shifts = [1] * (r-1) + [k-r+1]
            assert all(1 <= j <= D for j in shifts)
            assert s + sum(shifts)*M == n


def exhaustive_one_scale():
    # r=2, p=3, i=0, m=1. All 27 deterministic tables.
    total = 0
    for values in product(range(3), repeat=3):
        A = {x + 3*values[x] for x in range(3)}
        total += energy(cyclic_counts(A, 2, 9))
    assert total <= 27 * factorial(2) * (1+3) * 9
    # Distinct residues mod 3 rule out all nondiagonal collisions except
    # three-term progressions. Each of the three candidate centers works
    # in one third of the tables and then contributes 4 energy.
    assert total == 27 * (15 + 4), total


if __name__ == "__main__":
    cases = [(2, 3, 1), (2, 3, 2), (2, 3, 3), (2, 3, 4),
             (3, 5, 1), (3, 5, 2), (4, 5, 1), (5, 7, 1)]
    total_cases = 0
    for r, p, m in cases:
        for seed in range(6):
            verify(r, p, m, seed, do_union=(p**(r*m) <= 20000))
            total_cases += 1
    lifts()
    exhaustive_one_scale()
    print(f"Verified {total_cases} digital systems, 3 lift ranges and 27 exact tables.")

