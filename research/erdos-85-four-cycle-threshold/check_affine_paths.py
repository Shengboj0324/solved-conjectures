#!/usr/bin/env python3
"""Exact regression for the path-charging hypotheses of POLARITY-EDIT-BARRIER.md."""
from collections import Counter
from random import Random


def verify(q, modulus):
    def mul(a, b):
        out = 0
        while b:
            if b & 1:
                out ^= a
            b >>= 1
            a <<= 1
            if a & q:
                a ^= modulus
        return out

    # The inverses certify that the specified finite ring is a field.
    assert all(any(mul(a, b) == 1 for b in range(1, q)) for a in range(1, q))
    n = q*q
    neighbors = []
    for v in range(n):
        a, b = divmod(v, q)
        near = {c*q + (b ^ mul(a, c)) for c in range(q)}
        assert (v in near) == (v < q)
        near.discard(v)
        neighbors.append(near)
    for u in range(n):
        assert len(neighbors[u]) == q - (u < q)
        assert all(u in neighbors[v] for v in neighbors[u])
    seen_pairs = set()
    for j in range(n):
        near = sorted(neighbors[j])
        for i, u in enumerate(near):
            for v in near[i+1:]:
                assert (u, v) not in seen_pairs
                seen_pairs.add((u, v))

    table = {}
    checks = 0
    for u in range(q):
        for v in range(n):
            if v == u or v in neighbors[u]:
                continue
            first = set()
            last = set()
            paths = []
            for x in neighbors[u]:
                common = neighbors[x] & neighbors[v]
                for y in common:
                    assert len({u, x, y, v}) == 4
                    assert x not in first and y not in last
                    first.add(x)
                    last.add(y)
                    paths.append((x, y))
            assert len(paths) >= q-2
            table[u, v] = paths
            checks += len(paths)
    rng = Random(85 + q)
    choices = [[v for v in range(n) if (u, v) in table] for u in range(q)]
    for _ in range(100):
        front = Counter()
        middle = Counter()
        for u in range(q):
            v = rng.choice(choices[u])
            for x, y in table[u, v]:
                front[tuple(sorted((u, x)))] += 1
                middle[tuple(sorted((x, y)))] += 1
        assert max(front.values()) == 1
        assert max(middle.values()) <= 2
    # Independent check of the arbitrary-line charging in the stronger proof.
    lines = [(set(range(a*q, (a+1)*q)), None) for a in range(q)]
    for center in range(n):
        raw = set(neighbors[center])
        if center < q:
            raw.add(center)
        lines.append((raw, center))
    rng.shuffle(lines)
    arbitrary_lines = 0
    for line, center in lines[:min(120, len(lines))]:
        front, middle = Counter(), Counter()
        for u in line:
            v = rng.choice([v for v in range(n) if v != u and v not in neighbors[u]])
            paths = []
            for x in neighbors[u]:
                for y in neighbors[x] & neighbors[v]:
                    assert len({u, x, y, v}) == 4
                    if center not in (x, y):
                        paths.append((x, y))
            assert len(paths) >= q-6
            assert len({x for x, _ in paths}) == len({y for _, y in paths}) == len(paths)
            for x, y in paths:
                front[tuple(sorted((u, x)))] += 1
                middle[tuple(sorted((x, y)))] += 1
        assert max(front.values(), default=0) <= 2
        assert max(middle.values(), default=0) <= 2
        arbitrary_lines += 1
    return len(table), checks, arbitrary_lines


if __name__ == "__main__":
    total_pairs = total_paths = total_lines = 0
    for q, f in ((4, 0b111), (8, 0b1011), (16, 0b10011), (32, 0b100101)):
        p, t, big = verify(q, f)
        total_pairs += p
        total_paths += t
        total_lines += big
        print(f"q={q}: {p} possible new pairs, {t} old simple paths.", flush=True)
    print(f"Total {total_pairs} pairs, {total_paths} paths and 400 seeded charging tests on the loop line. Checked {total_lines} arbitrary-line selections.")
