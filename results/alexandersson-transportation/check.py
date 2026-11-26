"""Compute transportation Ehrhart numerators from margins and certify nonreal roots."""

from fractions import Fraction
from math import comb


def tables(m, k):
    # states[a][b] counts partial columns with top row sums a and b.
    states = [[0] * (k + 1) for _ in range(k + 1)]
    states[0][0] = 1
    for margin in [2 * k] + [k] * m:
        new = [[0] * (k + 1) for _ in range(k + 1)]
        for a, row in enumerate(states):
            for b, count in enumerate(row):
                if count:
                    for x in range(min(k - a, margin) + 1):
                        for y in range(min(k - b, margin - x) + 1):
                            new[a + x][b + y] += count
        states = new
    return states[k][k]


def derivative(p):
    return [j * p[j] for j in range(1, len(p))]


def evaluate(p, x):
    value = 0
    for c in reversed(p):
        value = value * x + c
    return value


def sturm(p):
    chain = [p, derivative(p)]
    while True:
        rem = list(map(Fraction, chain[-2]))
        divisor = chain[-1]
        while len(rem) >= len(divisor):
            shift = len(rem) - len(divisor)
            coeff = rem[-1] / divisor[-1]
            for j, a in enumerate(divisor):
                rem[shift + j] -= coeff * a
            while rem and rem[-1] == 0:
                rem.pop()
        if not rem:
            break
        # Positive rescaling of a negative remainder preserves the Sturm chain.
        chain.append([-a / abs(rem[-1]) for a in rem])
    assert len(chain[-1]) == 1

    def variations(signs):
        return sum(a * b < 0 for a, b in zip(signs, signs[1:]))

    left = variations([(-1) ** (len(f) - 1) * f[-1] for f in chain])
    right = variations([f[-1] for f in chain])
    return left, right


def main():
    m = 12
    dim = 2 * m
    values = [tables(m, k) for k in range(dim + 1)]
    numerator = [sum((-1)**j * comb(dim + 1, j) * values[k - j] for j in range(k + 1))
                 for k in range(dim + 1)]
    expected = [comb(m, j)**2 - (m if j == 1 else 0) for j in range(m + 1)]
    assert numerator == expected + [0] * (dim - m)
    x = Fraction(-1, 5)
    p, dp, ddp = expected, derivative(expected), derivative(derivative(expected))
    witness = (evaluate(dp, x)**2 - evaluate(p, x) * evaluate(ddp, x)) * 5**22
    assert witness == -389210787898375728
    left, right = sturm(p)
    assert left - right == 10
    print(f'{len(values)} dilations checked, degree {m}, squarefree.')
    print(f'Sturm variations at infinity: {left}, {right}. Real roots: {left-right}.')
    print(f'Scaled Laguerre difference: {witness}.')


if __name__ == '__main__':
    main()
