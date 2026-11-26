"""Check the matching repair and the nullspace witness claim on small inputs."""

from itertools import combinations, product


def facet_matching(n, q):
    """Try every coloring of the empty set and singletons at face size three."""
    triples = list(combinations(range(n), 3))
    facets = [list(combinations(y, 2)) for y in triples]
    eligible_cases = repaired_requests = 0
    for colors in product(range(q), repeat=n + 1):
        requests = []
        loads = {}
        for i, face in enumerate(triples):
            seen = {colors[0], *(colors[x + 1] for x in face)}
            for c in set(range(q)) - seen:
                requests.append((i, c))
                for facet in facets[i]:
                    loads[facet] = loads.get(facet, 0) + 1
        if any(load > 3 for load in loads.values()):
            continue

        owner = {}

        def augment(request, visited):
            for facet in facets[request[0]]:
                if facet in visited:
                    continue
                visited.add(facet)
                if facet not in owner or augment(owner[facet], visited):
                    owner[facet] = request
                    return True
            return False

        for request in requests:
            assert augment(request, set())
        assert len(owner) == len(requests)
        for i, face in enumerate(triples):
            seen = {colors[0], *(colors[x + 1] for x in face)}
            seen.update(owner[f][1] for f in facets[i] if f in owner)
            assert seen == set(range(q))
        eligible_cases += 1
        repaired_requests += len(requests)
    return eligible_cases, repaired_requests


def forced_circuits():
    """Enumerate rank-two binary matrices on five labeled elements."""
    # Three columns make a face of nullity one when their rank is two.
    matrices = circuits = 0
    for columns in product(range(4), repeat=5):
        if len(set(columns) - {0}) < 2:
            continue
        zero_sums = []
        for mask in range(1, 1 << len(columns)):
            total = 0
            for i, column in enumerate(columns):
                if mask & (1 << i):
                    total ^= column
            if total == 0:
                zero_sums.append(mask)
        minimal = {x for x in zero_sums if not any(y != x and y & x == y for y in zero_sums)}
        forced = set()
        for face in range(1 << len(columns)):
            if face.bit_count() != 3:
                continue
            candidates = [x for x in zero_sums if x & face == x]
            if len(candidates) == 1:
                forced.add(candidates[0])
        assert minimal == forced
        matrices += 1
        circuits += len(minimal)
    return matrices, circuits


if __name__ == "__main__":
    for n, q in [(4, 4), (5, 3)]:
        cases, repairs = facet_matching(n, q)
        assert cases and repairs
        print(f"{n} points, {q} colors: {cases} qualifying colorings, {repairs} matched requests")
    matrices, circuits = forced_circuits()
    print(f"{matrices} rank-two matrices, {circuits} circuits forced on nullity-one faces")
