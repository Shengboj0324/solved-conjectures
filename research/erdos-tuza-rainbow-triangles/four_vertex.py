"""Verify the four-vertex obstruction by integer arithmetic on all colorings."""

from itertools import combinations, permutations, product
from json import loads
from pathlib import Path


COLORS = range(6)
PALETTES = {tuple(map(int, t)) for t in ('012', '013', '014', '015', '023',
                                        '024', '035', '045', '125', '134')}


def read_weights():
    triples = list(combinations(range(3), 2))
    edge_index = {edge: i for i, edge in enumerate(triples)}
    automorphisms = [p for p in permutations(COLORS)
                     if {tuple(sorted(p[c] for c in t)) for t in PALETTES} == PALETTES]
    weights = {}
    records = loads(Path(__file__).with_name('four-vertex-weights.json').read_text())
    for colors, root, tested, weight in records:
        for color_map in automorphisms:
            for order in permutations(range(3)):
                indices = [edge_index[tuple(sorted((order[i], order[j])))] for i, j in triples]
                relabeled = tuple(color_map[colors[index]] for index in indices)
                key = (relabeled, order.index(root), color_map[tested])
                assert weights.setdefault(key, weight) == weight
    return weights


def main():
    weights = read_weights()
    edges = list(combinations(range(4), 2))
    index = {edge: i for i, edge in enumerate(edges)}
    omissions = []
    for omitted in range(4):
        triangle = sorted(set(range(4)) - {omitted})
        internal = [index[e] for e in combinations(triangle, 2)]
        external = [index[tuple(sorted((r, omitted)))] for r in triangle]
        omissions.append((internal, external))
    scores = []
    for colors in product(COLORS, repeat=6):
        total = 0
        for internal, external in omissions:
            flag = tuple(colors[j] for j in internal)
            if len(set(flag)) == 3 and tuple(sorted(flag)) not in PALETTES:
                break
            for root, test_edge in enumerate(external):
                row = [weights.get((flag, root, c), 0) for c in COLORS]
                total += 6 * row[colors[test_edge]] - sum(row)
        else:
            assert total > 0
            scores.append(total)
    print(f'{len(scores):,} allowed labeled colorings. Integer score range {min(scores)} to {max(scores)}.')
    assert min(scores) == 12 and max(scores) == 2878


if __name__ == '__main__':
    main()
