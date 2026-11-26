"""Count every projective line in an order-64 switched translation plane."""

from collections import Counter


def mul(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a & 64:
            a ^= 0b1000011
        b >>= 1
    return result


def power(a, s):
    result = 1
    for _ in range(s):
        result = mul(result, a)
    return result


field = range(64)
# Polynomial-basis encoding modulo t^6+t+1, with t represented by 2.
assert {power(2, i) for i in range(63)} == set(range(1, 64))
kernel = [x for x in field if power(x, 8) == x]
coordinate_frobenius = {
    a ^ mul(2, b): mul(a, a) ^ mul(2, mul(b, b)) for a in kernel for b in kernel
}
assert len(kernel) == 8 and len(coordinate_frobenius) == 64
slope = [
    [mul(a, power(x, 8) if power(a, 9) == 1 else x) for x in field]
    for a in field
]
lookup = {
    (x, slope[a][x]): a for a in field for x in range(1, 64)
}
assert len(lookup) == 63 * 64
points = {(x, mul(c, coordinate_frobenius[x])) for x in field for c in kernel if c}
secants = Counter()
for a in field:
    line_sizes = Counter(y ^ slope[a][x] for x, y in points)
    assert len(line_sizes) == 64
    secants.update(line_sizes.values())
vertical = Counter(x for x, y in points)
assert len(vertical) == 64
secants.update(v + 1 for v in vertical.values())  # Add vertical point at infinity.
secants[1] += 1
assert len(points) + 1 == 443 and sum(secants.values()) == 4161
assert min(secants) == 1 and max(secants) == 22
print(f'{len(points)+1} points, {sum(secants.values())} lines, secants {sorted(secants.items())}')


def pair_line(p1, p2):
    x, y = p1
    xx, yy = p2
    if x == xx:
        return (64, x)
    a = lookup[x ^ xx, y ^ yy]
    return a, y ^ slope[a][x]


def cross(l, ll):
    a, b = l
    aa, bb = ll
    if a == aa:
        return None
    if a == 64:
        return b, bb ^ slope[aa][b]
    if aa == 64:
        return bb, b ^ slope[a][bb]
    x = next(x for x in field if slope[a][x] ^ slope[aa][x] == b ^ bb)
    return x, b ^ slope[a][x]


# Two triples on the lines x=0 and x=1 violate Pappus's theorem.
a, b, c = (0, 0), (0, 1), (0, 2)
u, v, w = (1, 0), (1, 2), (1, 3)
x = cross(pair_line(a, v), pair_line(u, b))
y = cross(pair_line(a, w), pair_line(u, c))
z = cross(pair_line(b, w), pair_line(v, c))
assert (x, y, z) == ((8, 16), (2, 6), (32, 2))
assert pair_line(x, y) == (41, 23) and pair_line(x, z) == (15, 43)
print(f"Pappus intersections {x}, {y}, {z} are noncollinear")
