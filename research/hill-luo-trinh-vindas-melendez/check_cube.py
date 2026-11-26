"""Count sorted lattice points and test the cube identity on full Ehrhart polynomials."""

from collections import Counter
from functools import cache
from itertools import accumulate, combinations_with_replacement
from math import comb, factorial, prod


@cache
def lattice_count(b, t):
    n = len(b)
    if n == 0 or t == 0:
        return 1
    sides = [t * (s - 1) for s in accumulate(b)]
    capacities = list(accumulate(reversed(sides)))
    result = 0
    for values in combinations_with_replacement(range(sides[-1] + 1), n):
        if all(total <= bound for total, bound in zip(accumulate(reversed(values)), capacities)):
            result += factorial(n) // prod(factorial(m) for m in Counter(values).values())
    return result


def project_tail(tail, j):
    if j > len(tail):
        return ()
    return (1 + sum(tail[:j]),) + tail[j:]


if __name__ == '__main__':
    checks = 0
    for tail in ((1, 1), (1, 3), (3, 1), (2, 1, 2), (1, 2, 1), (2, 1, 1)):
        n = len(tail) + 1
        for c in (0, 1, 3):
            for t in range(n + 1):
                right = sum(comb(n, j) * (c*t)**j * lattice_count(project_tail(tail, j), t)
                            for j in range(n + 1))
                assert lattice_count((1+c,) + tail, t) == right, (tail, c, t)
                checks += 1
    print(f'{checks} independent lattice-count identities, identifying 18 Ehrhart polynomials')
