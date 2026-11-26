"""Check the spoke identity, block-pair parity and supersaturation bound."""
from itertools import combinations
from random import Random


def binary_projective(dimension):
    n = 2**dimension - 1
    blocks = [(x-1, y-1, (x ^ y)-1) for x in range(1, n+1)
              for y in range(x+1, n+1) if y < (x ^ y)]
    return n, blocks


def bose(group_order):
    """The Bose system on three levels of an odd cyclic group."""
    n = 3 * group_order
    vertex = lambda x, level: 3*x + level
    blocks = [(3*x, 3*x+1, 3*x+2) for x in range(group_order)]
    inverse_two = (group_order + 1) // 2
    for x, y in combinations(range(group_order), 2):
        midpoint = (x+y)*inverse_two % group_order
        for level in range(3):
            blocks.append((vertex(x, level), vertex(y, level),
                           vertex(midpoint, (level+1) % 3)))
    return n, blocks


def check(n, blocks, colors, inspect_block_pairs):
    owner = [[-1]*n for _ in range(n)]
    memberships = []
    for index, block in enumerate(blocks):
        memberships.append(set(block))
        for x, y in combinations(block, 2):
            assert x != y and owner[x][y] == -1
            owner[x][y] = owner[y][x] = index
    assert all(owner[x][y] >= 0 for x, y in combinations(range(n), 2))
    degree = [sum(colors[k] for k in row if k != -1) for row in owner]
    imbalance = sum((2*d - (n-1))**2 for d in degree)
    counts = [0]*4
    for k, (a, b, c) in enumerate(blocks):
        for p in range(n):
            if p in memberships[k]:
                continue
            spokes = (owner[p][a], owner[p][b], owner[p][c])
            assert len(set(spokes)) == 3 and k not in spokes
            j = sum(colors[i] == colors[k] for i in spokes)
            counts[j] += 1
    _, odd_one, _, sails = counts
    assert 2*odd_one == 6*sails + 2*n*(n-1) - imbalance
    assert sum(counts) == n*(n-1)*(n-3)//6
    red = sum(colors)
    blue = len(blocks)-red
    assert 16*red*blue <= 9*n*(n-1)**2 + 32*(n-1)*sails
    assert 144*red*blue >= n*n*(n-1)*(n-3) - 6*n*sails
    assert (294*n-288)*sails >= n*(n-1)*(n*(n-3)-81*(n-1))
    disjoint = 0
    if inspect_block_pairs:
        for i, j in combinations(range(len(blocks)), 2):
            if colors[i] == colors[j] or memberships[i] & memberships[j]:
                continue
            rows = [sum(colors[owner[x][y]] == colors[j] for y in blocks[j])
                    for x in blocks[i]]
            columns = [sum(colors[owner[x][y]] == colors[i] for x in blocks[i])
                       for y in blocks[j]]
            assert any(count % 2 for count in rows + columns)
            disjoint += 1
    return sails, disjoint


def main():
    total = pairs = 0
    for n, blocks in (binary_projective(3), bose(3)):
        limits = []
        for mask in range(1 << len(blocks)):
            colors = [(mask >> i) & 1 for i in range(len(blocks))]
            sails, disjoint = check(n, blocks, colors, True)
            limits.append(sails)
            pairs += disjoint
        total += len(limits)
        print(n, 'all colorings', len(limits), 'sail range', min(limits), max(limits))
    print('exhaustive colorings', total, 'disjoint opposite block pairs', pairs)

    rng = Random(813)
    for n, blocks in (bose(29), binary_projective(7)):
        colorings = [[0]*len(blocks), [i % 2 for i in range(len(blocks))],
                     [int(min(block) < n//6) for block in blocks]]
        for probability in (0.1, 0.3, 0.5, 0.8):
            colorings.append([int(rng.random() < probability) for _ in blocks])
        values = [check(n, blocks, colors, False)[0] for colors in colorings]
        print(n, 'larger colorings', len(values), 'sail range', min(values), max(values))


if __name__ == '__main__':
    main()
