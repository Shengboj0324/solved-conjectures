#!/usr/bin/env python3
"""Independently check the mixed Nordhaus–Gaddum construction on finite graphs."""
from functools import lru_cache
from itertools import combinations
from random import Random


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def graph(n, edges):
    rows = [0] * n
    for u, v in edges:
        rows[u] |= 1 << v
        rows[v] |= 1 << u
    return rows


def components(rows, vertices):
    while vertices:
        seen = wave = vertices & -vertices
        while wave:
            nxt = 0
            for v in bits(wave):
                nxt |= rows[v]
            wave = nxt & vertices & ~seen
            seen |= wave
        yield seen
        vertices ^= seen


def metric(rows):
    n = len(rows)
    dist = [[n + 1] * n for _ in rows]
    for i in range(n):
        dist[i][i] = 0
        for j in bits(rows[i]):
            dist[i][j] = 1
    for k in range(n):
        for i in range(n):
            for j in range(n):
                dist[i][j] = min(dist[i][j], dist[i][k] + dist[k][j])
    return dist


def check(rows):
    n = len(rows)
    all_v = (1 << n) - 1
    rev = [all_v ^ ((1 << i) | row) for i, row in enumerate(rows)]
    dist = metric(rows)

    @lru_cache(None)
    def independent_l(mask):
        if not mask:
            return True
        x = (mask & -mask).bit_length() - 1
        return not (rev[x] & mask) and independent_l(mask ^ (1 << x))

    @lru_cache(None)
    def chi_l(mask):
        if not mask:
            return 0
        pivot = mask & -mask
        candidates = (mask ^ pivot) & ~rev[pivot.bit_length() - 1]
        best = mask.bit_count()
        subset = candidates
        while True:
            group = subset | pivot
            if independent_l(group):
                best = min(best, 1 + chi_l(mask ^ group))
            if not subset:
                return best
            subset = (subset - 1) & candidates

    @lru_cache(None)
    def matching(mask):
        if not mask:
            return ()
        x = (mask & -mask).bit_length() - 1
        rem = mask ^ (1 << x)
        best = matching(rem)
        for y in bits(rem & rev[x]):
            ans = ((x, y),) + matching(rem ^ (1 << y))
            if len(ans) > len(best):
                best = ans
        return best

    def valid(group):
        if any(rows[x] >> y & 1 for x, y in combinations(group, 2)):
            return False
        for x, y, z in combinations(group, 3):
            vals = sorted((dist[x][y], dist[y][z], dist[z][x]))
            if vals[-1] <= n and vals[0] + vals[1] == vals[2]:
                return False
        return True

    colors = []
    roots_checked = merged_classes = 0
    for component in components(rows, all_v):
        k = chi_l(component)
        w = component
        for v in bits(component):
            if chi_l(w ^ (1 << v)) == k:
                w ^= 1 << v
        assert all(chi_l(w ^ (1 << v)) < k for v in bits(w))
        order = []
        unused = set(bits(component ^ w))
        if unused:
            order.append(min(unused))
            unused.remove(order[-1])
        while unused:
            u = min(unused, key=lambda v: (dist[order[-1]][v], v))
            unused.remove(u)
            order.append(u)
        groups = [[order[j - 1]] if j else [] for j in range(len(order))]
        if order:
            groups.append([order[-1]])
        local = []
        for block in components(rows, w):
            ki = chi_l(block)
            assert all(chi_l(block ^ (1 << x)) == ki - 1 for x in bits(block))
            for x in bits(block):
                assert len(matching(block ^ (1 << x))) >= ki - 1
                roots_checked += 1
            if order:
                j = next(j for j, u in enumerate(order) if rows[u] & block)
                root = next(bits(rows[order[j]] & block))
                groups[j].append(root)
            else:
                root = next(bits(block))
                groups.append([root])
            rest = set(bits(block)) - {root}
            for x, y in matching(block ^ (1 << root))[:ki - 1]:
                local.append([x, y])
                rest.difference_update((x, y))
            local.extend([x] for x in sorted(rest))
        merged_classes += sum(len(group) >= 3 for group in groups)
        local += [group for group in groups if group]
        assert len(local) <= component.bit_count() - k + 1
        while len(colors) < len(local):
            colors.append([])
        for i, group in enumerate(local):
            colors[i].extend(group)
    assert sorted(v for group in colors for v in group) == list(range(n))
    assert all(valid(group) for group in colors)
    assert len(colors) + chi_l(all_v) <= n + 1
    return roots_checked, merged_classes


if __name__ == "__main__":
    rng = Random(26061126)
    graphs = roots = merged = 0
    for n in range(7):
        edges = list(combinations(range(n), 2))
        for mask in range(1 << len(edges)):
            r, m = check(graph(n, (edges[i] for i in bits(mask))))
            graphs, roots, merged = graphs + 1, roots + r, merged + m
    print(f"All {graphs} labelled graphs through order six; {roots} prescribed roots.", flush=True)
    for j in range(2000):
        n = rng.randrange(7, 13)
        rate = rng.uniform(.04, .91)
        ed = {p for p in combinations(range(n), 2) if rng.random() < rate}
        if j % 4 == 0:
            ed.update((i, i+1) for i in range(n-1))
        if j % 4 == 1:
            ed.update((i, min(n-1, i+2)) for i in range(n-1) if rng.random() < .7)
        r, m = check(graph(n, sorted(ed)))
        graphs, roots, merged = graphs + 1, roots + r, merged + m
    assert merged
    print(f"Total {graphs} graphs, {roots} prescribed roots; {merged} assembled classes of size >= 3.")
