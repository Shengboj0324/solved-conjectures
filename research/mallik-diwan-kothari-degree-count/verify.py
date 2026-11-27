"""Exact checks: literal matchings on 16 vertices and Hall across the family."""
from functools import lru_cache
from itertools import combinations


def graph(k, t):
    n = k + t
    r = 2 * k - t
    high_bits = (1 << k) - 1
    low_bits = ((1 << n) - 1) ^ high_bits
    return tuple(
        (low_bits | (1 << i if i < r else 0))
        if i < k else (high_bits | (1 << i))
        for i in range(n)
    )


def degrees(rows):
    return [row.bit_count() for row in rows] + [
        sum(bool(row & (1 << j)) for row in rows) for j in range(len(rows))
    ]


def connected(rows):
    left, right = 1, 0
    while True:
        new_right = right
        for i, row in enumerate(rows):
            if left & (1 << i):
                new_right |= row
        new_left = sum(1 << i for i, row in enumerate(rows) if row & new_right)
        if (new_left, new_right) == (left, right):
            return left == right == (1 << len(rows)) - 1
        left, right = new_left, new_right


def deletions(rows):
    for i, row in enumerate(rows):
        for j in range(len(rows)):
            if row & (1 << j):
                yield rows[:i] + (row ^ (1 << j),) + rows[i + 1:]


def literal_extendability(rows, k):
    """Use the definition, not the Hall characterization."""
    n = len(rows)
    full = (1 << n) - 1
    edges = [(i, j) for i in range(n) for j in range(n) if rows[i] & (1 << j)]

    @lru_cache(maxsize=None)
    def perfect(left, right):
        if not left:
            return not right
        i = (left & -left).bit_length() - 1
        return any(
            perfect(left ^ (1 << i), right ^ (1 << j))
            for j in range(n)
            if rows[i] & right & (1 << j)
        )

    checked = 0
    for matching in combinations(edges, k):
        if len({i for i, _ in matching}) != k or len({j for _, j in matching}) != k:
            continue
        checked += 1
        left = full ^ sum(1 << i for i, _ in matching)
        right = full ^ sum(1 << j for _, j in matching)
        if not perfect(left, right):
            return False, matching
    return checked > 0 and connected(rows), checked


def hall(rows, k):
    """Compute all neighborhood unions by subset recurrence."""
    n = len(rows)
    neighbors = [0] * (1 << n)
    for mask in range(1, 1 << n):
        first = mask & -mask
        neighbors[mask] = neighbors[mask ^ first] | rows[first.bit_length() - 1]
        size = mask.bit_count()
        if size <= n - k and neighbors[mask].bit_count() < size + k:
            return False
    return True


def main():
    # Use the literal row masks from the independent edge-deletion search.
    rows = (108, 228, 116, 155, 187, 102, 101, 155)
    assert connected(rows)
    d = degrees(rows)
    assert (len(d), sum(d) // 2, d.count(4)) == (16, 36, 10)
    ok, checked = literal_extendability(rows, 3)
    assert ok
    deleted = list(deletions(rows))
    failures = [literal_extendability(subgraph, 3) for subgraph in deleted]
    assert len(failures) == 36 and all(not ok and isinstance(witness, tuple)
                                       for ok, witness in failures)
    print(f"Literal witness: {checked} three-edge matchings extend; "
          f"all {len(failures)} deletions have a nonextending matching.")

    count = 0
    for k in range(3, 8):
        for t in range(k + 2, 2 * k):
            rows = graph(k, t)
            r = 2 * k - t
            d = degrees(rows)
            n, m, low = len(d), sum(d) // 2, d.count(k + 1)
            assert n == 2 * (k + t) and m == 2 * k * t + t + r and low == 2 * t
            assert 2 * (m - n + 2 * k) - (2 * k - 1) * low == 2 * r
            assert connected(rows) and hall(rows, k)
            assert all(min(degrees(g)) <= k or not hall(g, k) for g in deletions(rows))
            count += 1
    print(f"Family: {count} exact Hall and all-edge minimality checks pass.")


if __name__ == "__main__":
    main()
