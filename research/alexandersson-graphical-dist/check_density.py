"""Check opposed endpoint responses against literal orientations of finite 2-trees."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb, prod


def conditional_counts(pages, sensor_precedes_other):
    counts = Counter()
    for gap in range(3):
        sensor_precedes_hub = gap >= (1 if sensor_precedes_other else 2)
        for j in range(pages + 1):
            ways = comb(pages, j) * 2 ** (j if sensor_precedes_hub else pages - j)
            counts[gap + j] += ways
    return counts


def compare(pages, sensors):
    # The vertex labels give the statistic's order: endpoints, satellites, hubs.
    first_hub = 2 + sum(pages)
    groups = []
    satellite = 2
    for i, (count, sensor) in enumerate(zip(pages, sensors)):
        hub = first_hub + i
        groups.append((hub, sensor, list(range(satellite, satellite + count))))
        satellite += count
    edges = [(0, 1)]
    for hub, sensor, leaves in groups:
        edges.extend([(0, hub), (1, hub)])
        for leaf in leaves:
            edges.extend([(sensor, leaf), (leaf, hub)])
    literal = Counter()
    for bits in range(1 << len(edges)):
        arcs = {(u, v) if bits >> i & 1 else (v, u) for i, (u, v) in enumerate(edges)}
        # A chordal graph has a directed cycle iff it has a directed triangle:
        # a chord of a shortest directed cycle would give a shorter one.
        if any((v, w) in arcs and (w, u) in arcs for u, v in arcs
               for w in range(first_hub + len(groups))):
            continue
        indices = tuple(sum((v, hub) in arcs for v in range(hub)) for hub, _, _ in groups)
        literal[(0, 1) in arcs, indices] += 1
    predicted = Counter()
    for forward in (False, True):
        marginals = [conditional_counts(count, forward == (sensor == 0))
                     for count, sensor in zip(pages, sensors)]
        for values in product(*(m.keys() for m in marginals)):
            predicted[forward, values] = prod(m[v] for m, v in zip(marginals, values))
    assert literal == predicted
    return sum(literal.values())


if __name__ == '__main__':
    totals = [compare(counts, sensors)
              for counts, sensors in [((1, 1, 1), (0, 0, 1)), ((2, 1), (1, 0))]]
    for pages in range(10):
        for forward in (False, True):
            weights = conditional_counts(pages, forward)
            assert set(weights) == set(range(pages + 3))
            assert sum(weights.values()) == 3**(pages + 1)
    # At the positive real point t=2 these rational parameters have P(2)=Q(2).
    def ratio(gamma):
        return (3 + 2 * gamma) / (3 + gamma)
    assert ratio(Fraction(1, 4))**2 == ratio(Fraction(81, 142))
    print(f'{sum(totals)} acyclic orientations; all filler supports and the rational tuning identity passed')
