"""Exact finite witnesses and a modest optional regression of the uniform proof."""
from itertools import combinations

SMALL = {4: [1], 5: [1], 8: [1, 4], 12: [2, 3], 13: [2, 3],
         18: [3, 4, 5], 21: [3, 4, 5], 24: [4, 5, 6, 7], 27: [4, 5, 6, 7]}


def symmetric(n, values):
    return set(values) | {(-x) % n for x in values}


def jumps(n):
    if n in SMALL:
        return symmetric(n, SMALL[n])
    k, r = divmod(n, 3)
    if r == 2:
        k += 1
        assert k >= 4
        return set(range(k, 2 * k))
    if r == 1:
        assert k >= 5
        return set(range(k, 2 * k + 2)) - {k + 1, 2 * k}
    assert k >= 10
    return set(range(k - 1, 2 * k + 2)) - {k, k + 2, 2 * k - 2, 2 * k}


def td(n, S):
    differences = {(a - b) % n for a in S for b in S}
    return (not S & differences
            and len(S | differences) == n and len(S) < n - 1)


def check(n, S):
    assert S and 0 not in S and S == symmetric(n, S) and td(n, S)
    nb = [sum(1 << ((v + x) % n) for x in S) for v in range(n)]
    c = 0
    for a, b in combinations(range(1, n), 2):
        if a in S or b in S or b - a in S:
            continue
        x, y, z = nb[0], nb[a], nb[b]
        assert sum(bool(t) for t in (x & y & ~z, y & z & ~x, z & x & ~y)) >= 2
        c += 1
    return c


def main():
    small = sum(check(n, jumps(n)) for n in SMALL)
    regression = sum(check(n, jumps(n)) for n in range(11, 241) if n != 15)
    survivors = []
    for mask in range(1 << 7):
        h = tuple(i + 1 for i in range(7) if mask >> i & 1)
        S = symmetric(15, h)
        if td(15, S):
            survivors.append(h)
            for x in range(15):
                assert {(t + x) % 15 for t in S} == {(t + x + 5) % 15 for t in S}
    assert survivors == [(1, 4, 6), (2, 3, 7)] or survivors == [(2, 3, 7), (1, 4, 6)]
    print(f"{small} small-witness and {regression:,} regression independent triples; "
          "the order-15 survivors of all 128 masks are exactly the two twin graphs.")


if __name__ == "__main__":
    main()
