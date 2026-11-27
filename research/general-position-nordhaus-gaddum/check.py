"""Check the constructive cover bound on labelled small graphs and seeded graphs."""
from itertools import combinations
import random


def parts(graph):
    left = set(graph)
    while left:
        todo = [min(left)]
        part = set(todo)
        left -= part
        for u in todo:
            for v in sorted(graph[u] & left):
                left.remove(v)
                part.add(v)
                todo.append(v)
        yield part


def dfs(graph, root):
    used, parents, post = {root}, {}, []

    def walk(u):
        for v in sorted(graph[u]):
            if v not in used:
                used.add(v)
                parents[v] = u
                walk(v)
        post.append(u)

    walk(root)
    assert used == set(graph)
    return parents, post


def color_from_cover(g, s):
    if len(g) <= 1:
        return [tuple(g)]
    o = set(g) - s
    components = list(parts({u: g[u] & s for u in s}))
    ci = {u: i for i, c in enumerate(components) for u in c}
    quotient = {i: set() for i in range(len(components))}
    for v in o:
        for i, j in combinations(sorted({ci[u] for u in g[v]}), 2):
            quotient[i].add(j)
            quotient[j].add(i)
    qp, qpost = dfs(quotient, 0)
    roots, internal_post, parents = {0: min(components[0])}, {}, {}
    for i in reversed(qpost):
        if i != 0:
            prev = qp[i]
            for t in internal_post[prev]:
                choices = {x for u in g[t] & o for x in g[u] & components[i]}
                if choices:
                    roots[i] = min(choices)
                    parents[roots[i]] = t
                    break
            assert i in roots
        uparent, internal_post[i] = dfs({u: g[u] & components[i]
                                         for u in components[i]}, roots[i])
        parents.update(uparent)
    order = [u for i in qpost for u in internal_post[i]]
    rank = {u: i for i, u in enumerate(order)}
    groups = {u: [] for u in s}
    for child, p in parents.items():
        groups[p].append(child)
    for v in o:
        groups[min(g[v], key=rank.__getitem__)].append(v)
    return [tuple(c) for c in groups.values() if c] + [(roots[0],)]


def dists(g):
    all_d = []
    for r in g:
        d = [len(g)] * len(g)
        d[r] = 0
        todo = [r]
        for u in todo:
            for v in g[u]:
                if d[v] == len(g):
                    d[v] = d[u] + 1
                    todo.append(v)
        all_d.append(d)
    return all_d


def check(g, cover, d):
    colors = color_from_cover(g, cover)
    assert len(colors) <= len(cover) + 1
    assert sorted(u for grp in colors for u in grp) == list(g)
    for grp in colors:
        for a, b in combinations(grp, 2):
            assert b not in g[a]
        for a, b, c in combinations(grp, 3):
            x, y, z = sorted((d[a][b], d[a][c], d[b][c]))
            assert x + y > z, (g, cover, grp)


def graph_of(n, edges):
    g = {i: set() for i in range(n)}
    for u, v in edges:
        g[u].add(v)
        g[v].add(u)
    return g


def main():
    small = big = 0
    for n in range(2, 7):
        all_edges = list(combinations(range(n), 2))
        for mask in range(1 << len(all_edges)):
            edges = [e for k, e in enumerate(all_edges) if mask >> k & 1]
            g = graph_of(n, edges)
            if len(next(parts(g))) != n:
                continue
            d = dists(g)
            edgemasks = [(1 << u) | (1 << v) for u, v in edges]
            for cover in range(1 << n):
                if all(cover & e for e in edgemasks):
                    check(g, {u for u in g if cover >> u & 1}, d)
                    small += 1
    rng = random.Random(1152992)
    for j in range(1000):
        n = rng.randrange(8, 55)
        edges = [(u, rng.randrange(u)) for u in range(1, n)]
        p = rng.choice([0, .02, .06, .15, .4, .8])
        edges += [e for e in combinations(range(n), 2) if rng.random() < p]
        g = graph_of(n, edges)
        d = dists(g)
        for _ in range(5):
            indep = set()
            for u in rng.sample(list(g), n):
                if not (g[u] & indep):
                    indep.add(u)
            check(g, set(g) - indep, d)
            big += 1
    print(f"{small:,} labelled connected graph-cover pairs through order 6 and "
          f"{big:,} seeded larger pairs passed all exact adjacency and shortest-path checks.")


if __name__ == "__main__":
    main()
