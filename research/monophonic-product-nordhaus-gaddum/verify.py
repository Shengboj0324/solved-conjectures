"""Exact independent check of the 45-vertex witness; standard library only."""

from itertools import combinations


def witness():
    s = 3
    k = 6 * s
    # Vertices of the prism are indexed ring-major. Each expands into 3 ports.
    prism = {tuple(sorted((r * s + i, r * s + (i + 1) % s)))
             for r in range(2) for i in range(s)}
    prism |= {(i, i + s) for i in range(s)}
    nb = [sorted(v if x == u else x for x, v in prism if u in (x, v))
          for u in range(2 * s)]

    def port(u, v):
        return 3 * u + nb[u].index(v)

    edges = {(3 * u + i, 3 * u + j)
             for u in range(2 * s) for i, j in combinations(range(3), 2)}
    edges |= {tuple(sorted((port(u, v), port(v, u)))) for u, v in prism}
    edges = sorted(edges)
    assert len(edges) == 27
    n = k + len(edges)
    adj = [0] * n
    for b, (u, v) in enumerate(edges, k):
        adj[b] = (1 << u) | (1 << v)
        adj[u] |= 1 << b
        adj[v] |= 1 << b
    centers = {port(u, u // s * s + (u % s + 1) % s) for u in range(2 * s)}
    return k, edges, adj, centers


def check_triples(k, adj):
    n = len(adj)
    cert = [[0] * n for _ in adj]
    path = []
    states = tails = 0

    def extend(u, taken, blocked):
        nonlocal states, tails
        states += 1
        candidates = adj[u] & ~taken & ~blocked
        if not candidates:
            # Every induced path can extend at both ends to a maximal one.
            # One orientation of each maximal path has increasing endpoints.
            if path[0] < u:
                tails += 1
                for x, y in combinations(path, 2):
                    if x > y:
                        x, y = y, x
                    cert[x][y] |= taken
            return
        while candidates:
            bit = candidates & -candidates
            candidates ^= bit
            v = bit.bit_length() - 1
            path.append(v)
            extend(v, taken | bit, blocked | adj[u])
            path.pop()

    for u in range(n):
        path.append(u)
        extend(u, 1 << u, 0)
        path.pop()

    stars = set()
    for u, v, w in combinations(range(n), 3):
        forbidden = u >= k and bool(adj[u] & adj[v] & adj[w])
        covered = bool((cert[u][v] >> w) & 1)
        assert covered != forbidden, (u, v, w, covered, forbidden)
        if forbidden:
            stars.add((u, v, w))
    return stars, states, tails


def exact_lower_by_center_masks(k, edges):
    edges_as_bits = [(1 << u) | (1 << v) for u, v in edges]
    # Every color is a star triple or has at most two vertices. For a
    # set of star centers U, all original vertices and all subdividers
    # of edges missing U must go in colors of size at most two.
    return min(mask.bit_count()
               + (k + sum(not (edge & mask) for edge in edges_as_bits) + 1) // 2
               for mask in range(1 << k))


def check_coloring(colors, adj, stars=None):
    assert sorted(sum((list(c) for c in colors), [])) == list(range(len(adj)))
    for color in colors:
        assert all(not (adj[u] >> v & 1) for u, v in combinations(color, 2))
        assert all(stars is not None and tuple(sorted(t)) in stars
                   for t in combinations(color, 3))


def main():
    k, edges, adj, centers = witness()
    n = len(adj)
    stars, states, tails = check_triples(k, adj)
    assert len(stars) == k
    rho = exact_lower_by_center_masks(k, edges)
    assert rho == 20
    big = [tuple(k + j for j, e in enumerate(edges) if c in e)
           for c in sorted(centers)]
    left = sorted(set(range(k, n)) - {v for b in big for v in b})
    pairs = [tuple(seq[j:j + 2])
             for seq in [list(range(k)), left] for j in range(0, len(seq), 2)]
    check_coloring(big + pairs, adj, stars)
    assert len(big + pairs) == rho
    complement = [((1 << n) - 1) ^ adj[u] ^ (1 << u) for u in range(n)]
    assert all(complement[i] >> j & 1 for i, j in combinations(range(k, n), 2))
    index = {e: k + j for j, e in enumerate(edges)}
    cpairs = [(u, index[tuple(sorted((u, u // 3 * 3 + (u % 3 + 1) % 3)))])
              for u in range(k)]
    cpairs += [(v,) for v in sorted(set(range(k, n)) - {b for _, b in cpairs})]
    check_coloring(cpairs, complement)
    sigma = len(edges)
    assert len(cpairs) == sigma == 27
    assert 4 * rho * sigma > (n + 1)**2
    print(f"{n} vertices; {states:,} induced-path states; {tails:,} terminal orientations; "
          f"all {len(stars)} exceptional triples are stars; {1 << k:,} center sets; "
          f"exact product {rho} × {sigma} = {rho*sigma} > {(n+1)**2//4}.")


if __name__ == "__main__":
    main()
