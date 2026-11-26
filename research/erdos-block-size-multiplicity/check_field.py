"""Exact finite checks of the direction-energy identity and subplane incidence count."""

from collections import Counter
from itertools import product
from random import Random


def multiplication_table(order, modulus):
    def multiply(x, y):
        value = 0
        while y:
            if y & 1:
                value ^= x
            x <<= 1
            if x & order:
                x ^= modulus
            y >>= 1
        return value

    table = [[multiply(x, y) for y in range(order)] for x in range(order)]
    assert all(len(set(row)) == order for row in table[1:])
    return table


def subfield(table, q):
    fixed = []
    for x, row in enumerate(table):
        power = 1
        for _ in range(q):
            power = row[power]
        if power == x:
            fixed.append(x)
    assert len(fixed) == q
    return fixed


def direction_energy(table, scalars):
    order = len(table)
    direction = [min(table[h][x] for h in scalars if h) for x in range(order)]
    for mask in range(1 << order):
        points = [x for x in range(order) if mask & (1 << x)]
        directions = Counter(direction[x ^ y] for x in points for y in points if x != y)
        by_directions = sum(count * count for count in directions.values())
        by_scalars = 0
        for h in scalars:
            if h:
                histogram = Counter(x ^ table[h][y] for x in points for y in points)
                by_scalars += sum(count * count for count in histogram.values()) - len(points) ** 2
        assert by_directions == by_scalars
    return 1 << order


def projective_points(elements):
    return ([(1, x, y) for x, y in product(elements, repeat=2)]
            + [(0, 1, y) for y in elements] + [(0, 0, 1)])


def subplane_lines(table, q):
    ambient = projective_points(range(len(table)))
    core = projective_points(subfield(table, q))
    core_set = set(core)
    incidences = []
    outer_degrees = Counter()
    for a, b, c in core:
        on_line = {p for p in ambient if not (table[a][p[0]] ^ table[b][p[1]] ^ table[c][p[2]])}
        assert len(on_line) == len(table) + 1
        inside = on_line & core_set
        assert len(inside) == q + 1
        incidences.append(inside)
        outer_degrees.update(on_line - core_set)
    assert max(outer_degrees.values()) == 1
    count = len(core)
    rng = Random(734)
    for size in range(count + 1):
        sample = set(rng.sample(core, size))
        occupancies = [len(sample & line) for line in incidences]
        assert sum(occupancies) == size * (q + 1)
        assert count * sum(x * x for x in occupancies) - sum(occupancies) ** 2 == q * size * (count-size)
    outside = len(ambient) - count
    return len(outer_degrees), outside - len(outer_degrees), count + 1


if __name__ == '__main__':
    small = multiplication_table(16, 0b10011)
    tested = direction_energy(small, subfield(small, 4))
    print(f'{tested} subsets of GF(16) passed the GF(4) direction-energy identity.')
    for order, modulus, q in [(8, 0b1011, 2), (16, 0b10011, 4), (64, 0b1000011, 4), (64, 0b1000011, 8)]:
        once, never, restrictions = subplane_lines(multiplication_table(order, modulus), q)
        print(f'GF({q}) inside GF({order}): {once} exterior points on one extension, '
              f'{never} on zero, {restrictions} exact variance checks.')
