"""Verify the six-path certificates and the covering of all switchings."""
from collections import Counter
from itertools import combinations
import json
from pathlib import Path


def seam_edges():
    edges = {}
    for y in range(6):
        for x in range(6):
            v = 6*y+x
            if x < 5:
                edges[v, v+1] = 0
            if y < 5:
                edges[v, v+6] = 0
    for x in range(6):
        edges[x, 35-x] = 1
    return edges


def forbidden_patterns(paths, edges):
    assert len(paths) == 6
    terminals = [paths[0][0], paths[0][-1], paths[1][-1], paths[2][-1]]
    assert len(set(terminals)) == 4 and terminals == sorted(terminals)
    parities = []
    interiors = set()
    for path, (a, b) in zip(paths, combinations(terminals, 2)):
        assert (path[0], path[-1]) == (a, b)
        assert len(set(path)) == len(path)
        middle = set(path[1:-1])
        assert not middle.intersection(terminals) and not middle.intersection(interiors)
        interiors.update(middle)
        parities.append(sum(edges[tuple(sorted((u, v)))] for u, v in zip(path, path[1:])) % 2)
    bits = [0, *(1-parity for parity in parities[:3])]
    for parity, (i, j) in zip(parities, combinations(range(4), 2)):
        assert parity ^ bits[i] ^ bits[j] == 1
    return tuple(-v-1 if bit else v+1 for v, bit in zip(terminals, bits))


def search(clauses, visits):
    """Return whether an assignment can avoid every forbidden pattern."""
    visits[0] += 1
    while clauses:
        if any(not clause for clause in clauses):
            return False
        unit = next((clause[0] for clause in clauses if len(clause) == 1), None)
        if unit is None:
            break
        clauses = [tuple(lit for lit in clause if lit != -unit)
                   for clause in clauses if unit not in clause]
    if not clauses:
        return True
    counts = Counter(abs(lit) for clause in clauses for lit in clause)
    variable = max(counts, key=counts.get)
    return search(clauses+[(variable,)], visits) or search(clauses+[(-variable,)], visits)


if __name__ == '__main__':
    certificates = json.loads(Path(__file__).with_name('grid-paths.json').read_text())
    edges = seam_edges()
    clauses = []
    for paths in certificates:
        pattern = forbidden_patterns(paths, edges)
        clauses += [pattern, tuple(-lit for lit in pattern)]
    visits = [0]
    assert not search(clauses, visits)
    print(len(certificates), 'subdivisions,', len(certificates)*6, 'paths,',
          len(clauses), 'forbidden patterns,', visits[0], 'search nodes; all switchings covered')
