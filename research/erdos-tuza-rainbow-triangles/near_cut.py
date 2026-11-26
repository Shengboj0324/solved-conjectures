"""Construct the near-cut colorings directly, using two overlapping cyclic cliques."""

from collections import Counter
from itertools import combinations


def coloring(h, d):
    assert h > 0 and h % 2 == 1 and d > 0 and d % 2 == 0
    m = h * d
    infinity = 2 * m
    edges = {}
    # In each copy of K_(m+1), infinity has residue zero. For each color
    # it sees d residues, paired by offsets j and -j.
    def internal_color(x, y):
        delta = abs(x - y)
        return (min(delta, m + 1 - delta) - 1) // (d // 2)

    classes = [[] for _ in range(h)]
    for residue in range(1, m + 1):
        classes[internal_color(0, residue)].append(residue)
    for shift in (0, m):
        for x, y in combinations(range(1, m + 1), 2):
            edges[shift + x - 1, shift + y - 1] = internal_color(x, y)
        for x in range(1, m + 1):
            edges[shift + x - 1, infinity] = internal_color(0, x)

    for x in range(1, m + 1):
        for y in range(1, m + 1):
            group = (internal_color(0, x) + internal_color(0, y)) % h
            edges[x - 1, m + y - 1] = h + group

    for even_color, residues in enumerate(classes):
        for x in residues[:d // 2]:
            a, b = x - 1, m + x - 1
            odd_color = edges[a, b]
            edges[a, b] = even_color
            edges[a, infinity] = edges[b, infinity] = odd_color
    return edges


def check(h, d):
    m = h * d
    n = 2 * m + 1
    edges = coloring(h, d)
    assert len(edges) == n * (n - 1) // 2
    degrees = [Counter() for _ in range(n)]
    errors = 0
    for (x, y), color in edges.items():
        assert 0 <= x < y < n
        degrees[x][color] += 1
        degrees[y][color] += 1
        crosses = x < m <= y
        errors += crosses != (color >= h)
    assert all(counts == dict.fromkeys(range(2 * h), d) for counts in degrees)
    assert errors == 3 * m // 2
    return len(edges)


if __name__ == "__main__":
    pairs = [(h, d) for h in (1, 3, 5, 7, 9) for d in (2, 4, 6, 8, 10)]
    count = sum(check(h, d) for h, d in pairs)
    print(f"{len(pairs)} balanced colorings, {count:,} edges, all cut discrepancies exact")
