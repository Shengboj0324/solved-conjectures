"""Exact graphical-dist counts, with a literal orientation check on small graphs."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb, factorial


def positive_bit(value):
    return 1 << (value - 1) if value else 0


def group_counts(pages, forward):
    """Weights by distinguished indegree, and weights with no page of indegree one."""
    total = [0] * (pages + 3)
    no_one = [0] * (pages + 3)
    for gap in range(3):
        after_u = gap >= (1 if forward else 2)
        for j in range(pages + 1):
            ways = comb(pages, j)
            total[gap + j] += ways * 2 ** (j if after_u else pages - j)
            # With all pages before u, each page is also before h if u precedes h.
            no_one[gap + j] += int(j == pages) if after_u else ways
    assert sum(total) == 3 ** (pages + 1)
    return total, no_one


def core_support(pages):
    counts = Counter()
    for forward in (False, True):
        total, no_one = group_counts(pages, forward)
        for i, j in product(range(len(total)), repeat=2):
            mask = positive_bit(i) | positive_bit(j)
            absent = 0 if forward else no_one[i] * no_one[j]
            counts[mask] += absent
            counts[mask | 1] += total[i] * total[j] - absent
    return {s: v for s, v in counts.items() if v}


def clique_support(size, extra):
    """An ordered clique followed by extra independent vertices adjacent to it."""
    masks = range(1 << size)
    counts = [(1 + mask.bit_count()) ** extra for mask in masks]
    # Counts so far and throughout this loop have support contained in mask.
    for d in range(1, size):
        for mask in masks:
            counts[mask] *= 1 + (mask & ((1 << d) - 1)).bit_count()
    for bit in range(size):
        for mask in masks:
            if mask & (1 << bit):
                counts[mask] -= counts[mask ^ (1 << bit)]
    return {mask: counts[mask] for mask in masks if counts[mask]}


def polynomial(pages, size, extra):
    core = core_support(pages)
    padding = clique_support(size, extra)
    coeff = [0] * (size + 3)
    for a, wa in core.items():
        for b, wb in padding.items():
            coeff[(a | b).bit_count()] += wa * wb
    assert sum(coeff) == 2 * 3 ** (2 * pages + 2) * factorial(size) * (size + 1) ** extra
    return coeff


def graph(pages, size, extra):
    """Vertex numbers are the specified earlier-neighbor order."""
    u, v = 0, 1
    h = [2 + 2 * pages, 3 + 2 * pages]
    edges = [(u, v)]
    for i, hub in enumerate(h):
        edges.extend([(u, hub), (v, hub)])
        for leaf in range(2 + i * pages, 2 + (i + 1) * pages):
            edges.extend([(u, leaf), (leaf, hub)])
    start = h[-1] + 1
    clique = [u, *range(start, start + size - 1)]
    edges.extend(combinations(clique, 2))
    for leaf in range(start + size - 1, start + size - 1 + extra):
        edges.extend((c, leaf) for c in clique)
    return start + size - 1 + extra, edges


def literal(pages, size, extra):
    n, edges = graph(pages, size, extra)
    coeff = [0] * (size + 3)
    for bits in product((0, 1), repeat=len(edges)):
        indegree, earlier = [0] * n, [0] * n
        outgoing = [[] for _ in range(n)]
        for (a, b), reverse in zip(edges, bits):
            if reverse:
                a, b = b, a
            outgoing[a].append(b)
            indegree[b] += 1
            earlier[b] += int(a < b)
        stack = [i for i in range(n) if not indegree[i]]
        visited = 0
        while stack:
            v = stack.pop()
            visited += 1
            for w in outgoing[v]:
                indegree[w] -= 1
                if not indegree[w]:
                    stack.append(w)
        if visited == n:
            coeff[len(set(earlier) - {0})] += 1
    return coeff


def main():
    for spec in ((0, 1, 0), (1, 2, 1), (2, 1, 0), (0, 3, 2)):
        assert literal(*spec) == polynomial(*spec)
    print('All orientations of four small ordered graphs checked directly against the formula.')
    pages, size, extra = 20, 10, 18
    n, edges = graph(pages, size, extra)
    p = polynomial(pages, size, extra)
    total = sum(p)
    q = [Fraction(a, total) for a in reversed(p)]
    x = Fraction(-7, 10)
    value = sum(a * x**k for k, a in enumerate(q))
    first = sum(k * a * x**(k-1) for k, a in enumerate(q) if k >= 1)
    second = sum(k * (k-1) * a * x**(k-2) for k, a in enumerate(q) if k >= 2)
    laguerre = first**2 - value * second
    assert laguerre < -Fraction(1, 40000)
    print(f'{n} vertices, {len(edges)} edges, degree {len(p)-1}, {total} acyclic orientations.')
    print('Normalized reciprocal Laguerre difference at -7/10:', laguerre)


if __name__ == '__main__':
    main()
