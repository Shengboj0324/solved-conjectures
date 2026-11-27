"""Classify the maximal intersecting triangle palettes using the proved tests."""

from collections import Counter
from itertools import combinations, permutations, product


COLORS = frozenset(range(6))
TRIPLES = tuple(frozenset(t) for t in combinations(sorted(COLORS), 3))


def main():
    pairs = [(t, COLORS - t) for t in TRIPLES if 0 in t]
    families = {frozenset(choices) for choices in product(*pairs)}
    assert len(families) == 1024
    partitions = set()
    for assignment in product(range(3), repeat=6):
        blocks = frozenset(frozenset(c for c in COLORS if assignment[c] == group) for group in range(3))
        if frozenset() not in blocks:
            partitions.add(blocks)
    assert len(partitions) == 90
    relabelings = list(permutations(range(6)))
    index = {t: k for k, t in enumerate(TRIPLES)}
    remaining = set(families)
    classes, survivors = 0, []
    designs, one_flip = set(), set()
    while remaining:
        family = min(remaining, key=lambda f: sum(1 << index[t] for t in f))
        orbit = {frozenset(frozenset(p[c] for c in t) for t in family) for p in relabelings}
        remaining.difference_update(orbit)
        classes += 1
        if set.intersection(*(set(t) for t in family)):
            continue
        if any(not any(all(t & block for block in partition) for t in family) for partition in partitions):
            continue
        degrees = Counter(c for t in family for c in t)
        degree_sequence = tuple(sorted(degrees.values()))
        survivors.append(degree_sequence)
        if degree_sequence == (5, 5, 5, 5, 5, 5):
            designs.update(orbit)
        if degree_sequence == (4, 4, 4, 6, 6, 6):
            one_flip.update(orbit)
    assert classes == 13
    assert sorted(survivors) == [(4, 4, 4, 4, 6, 8), (4, 4, 4, 6, 6, 6), (5, 5, 5, 5, 5, 5)]
    print(f'{len(families)} families, {classes} isomorphism classes, {len(survivors)} surviving classes')
    for values in sorted(survivors):
        print('color degrees', *values)

    # The four-vertex certificate excludes the third class. Maximal
    # extensions of an actual palette set differ by complementary swaps.
    assert len(designs) == 12 and len(one_flip) == 120
    surviving_families = designs | one_flip
    for family in surviving_families:
        neighbors = {
            (family - {t}) | {COLORS - t}
            for t in family
        } & surviving_families
        if family in designs:
            assert len(neighbors) == 10 and neighbors <= one_flip
            assert all(sum(pair <= t for t in family) == 2
                       for pair in map(frozenset, combinations(COLORS, 2)))
        else:
            assert len(neighbors) == 1 and neighbors <= designs
    print('The complementary-swap graph is 12 disjoint copies of K(1,10).')


if __name__ == '__main__':
    main()
