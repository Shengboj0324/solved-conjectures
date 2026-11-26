"""Fixture check for unique odd terminal paths. No third-party requirements."""
from random import Random

def paths(adj, start, end):
    def dfs(v, seen, d):
        if v == end:
            yield d
            return
        for w in adj[v]:
            if not seen >> w & 1:
                yield from dfs(w, seen | (1 << w), d + 1)
    return set(dfs(start, 1 << start, 0))

def cycles(adj):
    lens = set()
    def dfs(s, v, seen, d):
        if d >= 2 and s in adj[v]:
            lens.add(d + 1)
        for w in adj[v]:
            if w > s and not seen >> w & 1:
                dfs(s, w, seen | (1 << w), d + 1)
    for s in range(len(adj)):
        dfs(s, s, 1 << s, 0)
    return lens

def make(D, a, C):
    adj = [set() for _ in range(D + 1)]
    for i, j in [*((i, i + 1) for i in range(D)), *((i, D - j) for i, j in C)]:
        adj[i].add(j)
        adj[j].add(i)
    return adj

def compatible(p, q):
    (i, j), (k, l) = sorted((p, q))
    return i == k or j <= l or (k == i + 1 and j == l + 1)

def candidate(D, a):
    return [(i,j) for i in range(a + 1) for j in range(D - a) if (i + j) % 2]

def inspect(D, a, C, count):
    adj = make(D, a, C)
    pp = paths(adj, 0, D)
    if {x for x in pp if x % 2} != {D}:
        raise AssertionError((D, a, C, pp))
    ss = cycles(adj)
    labels = {(D - i - j) // 2 for i, j in C}
    assert {x for x in pp if not x % 2} == {D + 1 - 2*x for x in labels}
    assert {x for x in ss if x % 2} == {2*x + 1 for x in labels}
    even = {2*(x-z) + 2 for x in labels for z in labels if z < x}
    if any(i < k and j > l for i, j in C for k, l in C):
        even.add(4)
    assert {x for x in ss if not x % 2} == even
    count[1] += 1

def check_all():
    for D in (3, 5, 7, 9, 11):
        count = [0, 0]
        for a in range(D):
            P = candidate(D, a)
            def gen(ix, C):
                if ix == len(P):
                    inspect(D, a, C, count)
                    return
                gen(ix + 1, C)
                x = P[ix]
                if all(compatible(x, y) for y in C):
                    gen(ix + 1, C + [x])
            gen(0, [])
        print(f"odd path length={D}: verified={count[1]} other={count[0]}", flush=True)

def check_random():
    rng = Random(84)
    count = [0,0]
    for D in (13,15,17,19,21):
        for _ in range(400):
            a = rng.randrange(D)
            P = candidate(D, a)
            rng.shuffle(P)
            C = []
            for x in P:
                if rng.random() < .5 and all(compatible(x, y) for y in C):
                    C.append(x)
            inspect(D, a, C, count)
    print(f"wider randomized fixtures: verified={count[1]} other={count[0]}", flush=True)
if __name__ == '__main__':
    check_all()
    check_random()
