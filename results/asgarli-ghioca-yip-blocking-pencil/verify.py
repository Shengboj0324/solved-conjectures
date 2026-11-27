"""Check pencil minima and the specialization used in the written proof."""

from collections import Counter
from itertools import permutations, product
from math import gcd


class Field:
    """Polynomial-basis arithmetic modulo a monic irreducible over F_p."""

    def __init__(self, p, modulus):
        self.p = p
        self.e = len(modulus) - 1
        self.q = p**self.e
        self.elements = range(self.q)
        digits = [tuple(x // p**i % p for i in range(self.e)) for x in self.elements]

        def encode(coefficients):
            return sum((a % p) * p**i for i, a in enumerate(coefficients))

        def multiply(a, b):
            terms = [0] * (2 * self.e - 1)
            for i, x in enumerate(a):
                for j, y in enumerate(b):
                    terms[i + j] += x * y
            for i in reversed(range(self.e, len(terms))):
                for j in range(self.e):
                    terms[i - self.e + j] -= terms[i] * modulus[j]
            return encode(terms[:self.e])

        self.add = [[encode(x + y for x, y in zip(a, b)) for b in digits] for a in digits]
        self.mul = [[multiply(a, b) for b in digits] for a in digits]
        self.neg = [row.index(0) for row in self.add]
        self.inv = [0] + [row.index(1) for row in self.mul[1:]]
        assert all(len(set(row)) == self.q for row in self.mul[1:])

    def power(self, x, n):
        if n < 0:
            x, n = self.inv[x], -n
        result = 1
        while n:
            if n % 2:
                result = self.mul[result][x]
            x = self.mul[x][x]
            n //= 2
        return result

    def evaluate(self, coefficients, x):
        value = 0
        for coefficient in reversed(coefficients):
            value = self.add[self.mul[value][x]][coefficient]
        return value


def exact_minima(field):
    """Enumerate all shift sets and all lines, including non-prime fields."""
    add, mul, neg = field.add, field.mul, field.neg
    q, p, e = field.q, field.p, field.e
    results = []
    for j in range(1, e + 1):
        d = p**j
        constraints = set()
        for slope, intercept in product(field.elements, repeat=2):
            shifts = set()
            for x in field.elements:
                line_y = add[mul[slope][x]][intercept]
                shifts.add(add[field.power(x, d)][neg[line_y]])
            constraints.add(sum(1 << a for a in shifts))
        minimum = min(s.bit_count() for s in range(1 << q)
                      if all(s & line for line in constraints))
        g = gcd(e, j)
        assert minimum == 1 + (e // g) * (p**g - 1)
        results.append((d, minimum))
    print(f"F_{q}: all {1 << q} shift sets for each (degree, minimum) {results}")
    return len(results) * (1 << q)


def factor_degrees(field, coefficients):
    """Trial division by all possible monic factors up to half the degree."""
    d = len(coefficients) - 1
    add, mul, neg = field.add, field.mul, field.neg
    for size in range(1, d // 2 + 1):
        for terms in product(field.elements, repeat=size):
            remainder = list(coefficients)
            quotient = [0] * (d - size + 1)
            for index in reversed(range(len(quotient))):
                quotient[index] = remainder[index + size]
                for j, coefficient in enumerate(terms):
                    v = mul[quotient[index]][coefficient]
                    remainder[index + j] = add[remainder[index + j]][neg[v]]
            if not any(remainder[:size]):
                # A factor of the smallest possible degree is irreducible.
                return (size,) + factor_degrees(field, quotient)
    return (d,)


def check_specializations(field, d):
    add, mul, neg, power = field.add, field.mul, field.neg, field.power
    # All three graphs have the same leading coefficient, including nonmonic examples.
    c = field.q - 1
    graphs = [[(i + (i + 1) * j) % field.q for j in range(d)] + [c]
              for i in range(3)]
    counts = Counter()
    fiber_types = {}
    for u in range(1, field.q):
        multiplicities = Counter()
        for a in field.elements:
            seed = [neg[a], u] + [0] * (d - 2) + [c]
            if any(field.evaluate(seed, y) == 0 for y in field.elements):
                continue
            seed_type = factor_degrees(field, seed)
            # For degrees <= 4, a root-free polynomial has a repeated factor
            # only when it is the square of a quadratic; handle this explicitly.
            if seed_type == (2, 2):
                monic = [mul[v][field.inv[c]] for v in seed]
                if any([mul[b][b], add[mul[b][h]][mul[b][h]],
                        add[mul[h][h]][add[b][b]], add[h][h], 1] == monic
                       for b, h in product(field.elements, repeat=2)):
                    continue
            counts["regular seeds"] += 1
            for t in range(1, field.q):
                slope = mul[neg[u]][power(t, 1 - d)]
                intercept = mul[a][power(t, -d)]
                multiplicities[slope, intercept] += 1
                same = True
                misses = True
                for graph in graphs:
                    f = [mul[v][power(t, d - j)] for j, v in enumerate(graph)]
                    f[0], f[1] = add[f[0]][neg[a]], add[f[1]][u]
                    points = {x for x in field.elements
                              if field.evaluate(graph, x) == add[mul[slope][x]][intercept]}
                    roots = {y for y in field.elements if field.evaluate(f, y) == 0}
                    assert roots == {mul[t][x] for x in points}
                    key = tuple(f)
                    if key not in fiber_types:
                        fiber_types[key] = factor_degrees(field, f)
                    same &= fiber_types[key] == seed_type
                    misses &= not points
                    counts["graph-line tests"] += 1
                if same:
                    assert misses
                    counts["simultaneous type matches"] += 1
        assert max(multiplicities.values(), default=0) <= d - 1
    return counts


def check_quartic_twists():
    """Enumerate the rational points in both root-free twists of a quartic."""
    base = Field(3, (0, 1))
    quadratic = Field(3, (1, 0, 1))
    quartic = Field(3, (2, 1, 0, 0, 1))
    for pattern, ext in [((4,), quartic), ((2, 2), quadratic)]:
        fibers = Counter()
        for starts in permutations(ext.elements, len(pattern)):
            roots = []
            for start, length in zip(starts, pattern):
                x = start
                for _ in range(length):
                    roots.append(x)
                    x = ext.power(x, 3)
            if len(set(roots)) != 4:
                continue
            coefficients = [1]
            for x in roots:
                new = [0] + coefficients
                for j, a in enumerate(coefficients):
                    new[j] = ext.add[new[j]][ext.mul[a][ext.neg[x]]]
                coefficients = new
            assert all(x < 3 for x in coefficients)
            fibers[tuple(coefficients)] += 1
        expected = set()
        for low in product(base.elements, repeat=4):
            f = low + (1,)
            if factor_degrees(base, f) == pattern:
                if any(f == (b * b % 3, 2 * b * h % 3, (h * h + 2 * b) % 3,
                             2 * h % 3, 1) for b, h in product(base.elements, repeat=2)):
                    continue
                expected.add(f)
        assert fibers.keys() == expected
        assert set(fibers.values()) == ({4} if pattern == (4,) else {8})
        print(f"F_3 squarefree quartics of type {pattern}: {len(fibers)} fibers, "
              f"{sum(fibers.values())} rational orderings")


if __name__ == "__main__":
    fields = [Field(p, (0, 1)) for p in (3, 5, 7, 11)]
    fields.extend([Field(2, (1, 1, 1)), Field(2, (1, 1, 0, 1)),
                   Field(3, (1, 0, 1)), Field(2, (1, 1, 0, 0, 1))])
    check_quartic_twists()
    subsets = sum(exact_minima(f) for f in fields)
    totals = Counter()
    for f in fields:
        if f.q <= 11:
            for degree in (2, 3, 4):
                totals.update(check_specializations(f, degree))
    assert totals["simultaneous type matches"] > 0
    print(f"{subsets} shift-set checks; {dict(totals)}")
