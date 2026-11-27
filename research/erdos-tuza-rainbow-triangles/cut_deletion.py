"""Check the square-root vertex deletion construction and its parity witness."""

from itertools import combinations, islice
from math import isqrt


def construct(m):
    size = (1 + isqrt(1 + 4 * m)) // 2
    if size * (size - 1) < m:
        size += 1
    left = range(m)
    right = range(m, 2 * m + 1 - size)
    special = range(right.stop, 2 * m + 1)
    internal = set(islice(combinations(special, 2), m // 2))
    omitted = [x for x in special for _ in range(sum(x in edge for edge in internal))]
    assert len(omitted) == m
    edges = internal | {(a, b) for a in left for b in right}
    edges.update((a, x) for a in left for x in special if omitted[a] != x)
    assert all(sum(v in edge for edge in edges) == m for v in range(2 * m + 1))
    assert {edge for edge in edges if edge[1] < special.start} == {(a, b) for a in left for b in right}
    return edges, special


def main():
    for m in range(2, 41, 2):
        edges, special = construct(m)
        if m <= 8:
            vertices = range(2 * m + 1)
            odd_triangles = [set(t) for t in combinations(vertices, 3)
                             if sum(edge in edges for edge in combinations(t, 2)) % 2]
            assert all(set(special) & t for t in odd_triangles)
            assert all(any(t.isdisjoint(s) for t in odd_triangles)
                       for s in combinations(vertices, len(special) - 1))
    print('20 regular constructions and four exhaustive minimum-transversal checks passed.')


if __name__ == '__main__':
    main()
