"""Literal enumeration of maximal independent sets and their transversals."""
from itertools import combinations


def maximal_independent_sets(adj):
    n = len(adj)
    universe = (1 << n) - 1
    complement = [universe ^ ((1 << i) | a) for i, a in enumerate(adj)]

    def visit(chosen, candidates, excluded):
        if not (candidates | excluded):
            yield chosen
            return
        pivot = max(bits(candidates | excluded),
                    key=lambda i: (candidates & complement[i]).bit_count())
        for v in bits(candidates & ~complement[pivot]):
            b = 1 << v
            yield from visit(chosen | b, candidates & complement[v],
                             excluded & complement[v])
            candidates ^= b
            excluded |= b

    return list(visit(0, universe, 0))


def bits(mask):
    while mask:
        b = mask & -mask
        yield b.bit_length() - 1
        mask ^= b


def graph(m, r, sizes):
    labels = [a for a, s in enumerate(sizes) for _ in range(s)]
    n = m * r + len(labels)
    adj = [0] * n
    for a, b in combinations(range(n), 2):
        both_in_clique = b < m * r and a // m == b // m
        same_cross_label = a < m * r <= b and a % m == labels[b - m * r]
        if both_in_clique or same_cross_label:
            adj[a] |= 1 << b
            adj[b] |= 1 << a
    return adj


def main():
    graphs = independent_sets = hitting_checks = 0
    for m in range(2, 6):
        for r in range(1, m):
            for sizes in ((1,) * m, (2,) * m, (3,) * m, tuple(range(1, m + 1))):
                adj = graph(m, r, sizes)
                mis = maximal_independent_sets(adj)
                n = len(adj)
                all_vertices = (1 << n) - 1
                for I in mis:
                    covered = I
                    for v in bits(I):
                        assert not adj[v] & I
                        covered |= adj[v]
                    assert covered == all_vertices
                expected_i = r + sum(sorted(sizes)[:m-r])
                assert min(x.bit_count() for x in mis) == expected_i
                for T in combinations(range(n), r):
                    t = sum(1 << x for x in T)
                    assert any(not t & I for I in mis)
                    hitting_checks += 1
                U = sum(1 << (m * r + sum(sizes[:a])) for a in range(r + 1))
                assert all(U & I for I in mis)
                independent_sets += len(mis)
                graphs += 1
    print(f"{graphs} graphs, {independent_sets} maximal independent sets, "
          f"{hitting_checks} proposed smaller transversals rejected")


if __name__ == "__main__":
    main()
