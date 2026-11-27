#!/usr/bin/env python3
"""Independent exact minimax from the chosen set; no strategy data is used."""

V = tuple("ABCDEFGabcdefg")


def closed(v):
    # Row names are A..G and a..g, with each pair in the same column.
    neighbours = {v, v.swapcase()}
    col = ord(v.lower()) - ord("a")
    if col > 0:
        neighbours.add(chr(ord(v) - 1))
    if col < 6:
        neighbours.add(chr(ord(v) + 1))
    return neighbours


B = tuple(1 << j for j in range(len(V)))
N = tuple(sum(B[V.index(w)] for w in closed(v)) for v in V)
FULL = (1 << len(V)) - 1


def solve():
    union = [0] * (FULL + 1)
    for s in range(1, FULL + 1):
        bit = s & -s
        union[s] = union[s ^ bit] | N[bit.bit_length() - 1]

    win = [False] * (FULL + 1)
    for s in range(FULL, -1, -1):
        if union[s] != FULL:
            # A dominated but unchosen vertex is a legal option too.
            win[s] = any(not win[s | bit] for bit in B if not (s & bit))
    return win, union


if __name__ == "__main__":
    W, cover = solve()
    openings = tuple(v for bit, v in zip(B, V) if not W[bit])
    assert W[0] and openings == ("B", "F", "b", "f")
    assert cover[B[1]] != FULL
    print(f"Verified {len(W)} positions. Winning openings: {', '.join(openings)}.")
