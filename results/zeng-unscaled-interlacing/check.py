"""Check both strict interlacings by exact polynomial Euclidean remainders."""

from fractions import Fraction


def row(n, q, c):
    factors = [Fraction(1)]
    for k in range(1, n + 1):
        factors.append(factors[-1] * (1 - q**k) * (1 - c * q**(k - 1)))
    return [
        q ** (k * (k - 1)) * factors[n] / (factors[k] * factors[n - k])
        for k in range(n + 1)
    ]


def monic(poly):
    return [x / poly[-1] for x in poly]


def remainder(a, b):
    result = a[:]
    while len(result) >= len(b):
        factor = result[-1] / b[-1]
        shift = len(result) - len(b)
        for j, coefficient in enumerate(b):
            result[j + shift] -= factor * coefficient
        while result and not result[-1]:
            result.pop()
    return result


def strict_interlace(larger, smaller):
    """Monic signed remainder chains characterize strict real interlacing."""
    a, b = monic(larger), monic(smaller)
    assert len(a) == len(b) + 1
    while len(b) > 1:
        rem = remainder(a, b)
        assert len(rem) == len(b) - 1 and rem[-1] < 0
        a, b = b, monic(rem)


if __name__ == "__main__":
    parameter_pairs = 0
    chains = 0
    identities = 0
    for q in map(Fraction, ("1/4", "1/2", "3/4", "9/10")):
        for c in map(Fraction, ("1/9", "1/2", "3/4", "11/12")):
            parameter_pairs += 1
            for n in range(1, 8):
                p, higher = row(n, q, c), row(n + 1, q, c)
                for k in range(n + 1):
                    assert p[n-k] == q**((n-1)*(n-2*k)) * p[k]
                    assert higher[k] * (1 - q**(n+1-k)) * (1 - c*q**(n-k)) == (
                        (1 - q**(n+1)) * (1 - c*q**n) * p[k]
                    )
                    identities += 2
                smaller = [a * (-1)**k for k, a in enumerate(p)]
                for scale in (Fraction(1), q**2):
                    larger = [a * (-1/scale)**k for k, a in enumerate(higher)]
                    strict_interlace(larger, smaller)
                    chains += 1
    print(f"{parameter_pairs} parameter pairs, {chains} strict interlacing chains, "
          f"and {identities} coefficient identities passed.")
