"""Exact tests for square centering and the distinct-window dilation."""
from math import gcd, isqrt, lcm


def divisors(n):
    out = set()
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            out |= {d, n // d}
    return sorted(out)


def test_center():
    pairs = 0
    for q in range(2, 5001):
        ds = divisors(q)
        for i, a in enumerate(ds):
            for d in ds[i:]:
                D = q // a * d
                assert (q * q) % D == 0
                assert a * (D - q) == q * (d - a)
                u, v = D // gcd(D, q), q // gcd(D, q)
                assert q % (u * v) == 0 and gcd(u, v) == 1
                pairs += 1
    print(f"Checked {pairs} square centerings and reduced pairs.")


def test_dilation():
    windows = 0
    for a in range(20, 401):
        cluster = [a, a + 2, a + 3, a + 5]
        q = lcm(*cluster)
        span = cluster[-1] - a
        M = a // (4 * span)
        rows = [[s * d for d in cluster] for s in range(M, 2 * M)]
        A = [x for row in rows for x in row]
        assert all(x < y for x, y in zip(A, A[1:]))
        for offset, row in enumerate(rows):
            for k in range(1, len(cluster) + 1):
                j = offset * len(cluster)
                assert A[j:j+k] == row[:k]
                assert lcm(*A[j:j+k]) < 2 * M * q
                windows += 1
    print(f"Checked {windows} disjoint-prefix windows and their strict LCM bound.")


if __name__ == "__main__":
    test_center()
    test_dilation()
