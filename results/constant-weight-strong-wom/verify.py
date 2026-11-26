"""Reference encoder and decoder for exact-weight strong write-once memory."""

from dataclasses import dataclass
from itertools import combinations
from math import comb


def subsets(mask, weight):
    """Enumerate submasks of the requested weight."""
    positions = [1 << i for i in range(mask.bit_length()) if mask >> i & 1]
    for selected in combinations(positions, weight):
        yield sum(selected)


@dataclass
class Layer:
    bits: int
    labels: dict

    def read(self, mask):
        return self.labels[mask] if self.bits else 0


def build_layer(length, weight, available, block_limit):
    volume = comb(available, weight)
    bits = max(0, (volume // (4 * block_limit)).bit_length() - 1)
    if not bits:
        return Layer(0, {})
    colors = 1 << bits
    full = (1 << length) - 1
    incident = {mask: [] for mask in subsets(full, weight)}
    states = list(subsets(full, available))
    for index, state in enumerate(states):
        for mask in subsets(state, weight):
            incident[mask].append(index)

    # The conditional gain for witnessing a missing label with f local
    # words still available, scaled by the common denominator colors^(volume-1).
    gain = [0, colors ** (volume - 1)]
    for _ in range(1, volume):
        gain.append((gain[-1] // colors) * (colors - 1))
    remaining = [volume] * len(states)
    missing = [set(range(colors)) for _ in states]
    labels = {}
    for mask, neighbors in incident.items():
        scores = [0] * colors
        for index in neighbors:
            for color in missing[index]:
                scores[color] += gain[remaining[index]]
        chosen = max(range(colors), key=scores.__getitem__)
        labels[mask] = chosen
        for index in neighbors:
            remaining[index] -= 1
            missing[index].discard(chosen)
    assert not any(missing)
    return Layer(bits, labels)


class StrongWOM:
    def __init__(self, n, state_weight, output_weight, block_limit=None):
        if not 0 <= output_weight <= state_weight <= n or n < 1:
            raise ValueError("Require 0 <= output weight <= state weight <= n and n >= 1")
        self.n = n
        self.state_weight = state_weight
        self.output_weight = output_weight
        if block_limit is None:
            block_limit = max(1, n.bit_length() - 1)
        if not 1 <= block_limit <= n:
            raise ValueError("Block length must be between 1 and n")
        self.blocks = [(i, min(n - i, block_limit)) for i in range(0, n, block_limit)]
        self.layers = {}
        costs = {}
        for length in sorted({b for _, b in self.blocks}):
            for s in range(length + 1):
                for w in self.allowed(s):
                    if (length, w) not in self.layers:
                        self.layers[length, w] = build_layer(length, w, s, block_limit)
                costs[length, s] = min(self.layers[length, w].bits for w in self.allowed(s))

        best = {0: 0}
        for _, length in self.blocks:
            updated = {}
            for old, cost in best.items():
                for s in range(min(length, state_weight - old) + 1):
                    value = cost + costs[length, s]
                    if old + s not in updated or value < updated[old + s]:
                        updated[old + s] = value
            best = updated
        self.bits = best[state_weight]

    def allowed(self, available):
        floor, remainder = divmod(available * self.output_weight, max(1, self.state_weight))
        return (floor, floor + 1) if remainder else (floor,)

    def split(self, word):
        return [(word >> start) & ((1 << length) - 1) for start, length in self.blocks]

    def check_word(self, word, weight):
        if word < 0 or word.bit_length() > self.n or word.bit_count() != weight:
            raise ValueError("Word has the wrong length or weight")

    def encode(self, state, message):
        self.check_word(state, self.state_weight)
        if not 0 <= message < 1 << self.bits:
            raise ValueError("Message outside the code")
        pieces = self.split(state)
        options = [self.allowed(piece.bit_count()) for piece in pieces]
        weights = [v[0] for v in options]
        deficit = self.output_weight - sum(weights)
        for i, choices in enumerate(options):
            if deficit and len(choices) == 2:
                weights[i] += 1
                deficit -= 1
        assert deficit == 0
        layers = [self.layers[b, w] for (_, b), w in zip(self.blocks, weights)]
        left = sum(layer.bits for layer in layers)
        assert left >= self.bits
        padded = message << (left - self.bits)
        output = 0
        for (start, _), state_part, weight, layer in zip(self.blocks, pieces, weights, layers):
            left -= layer.bits
            label = (padded >> left) & ((1 << layer.bits) - 1)
            mask = next(mask for mask in subsets(state_part, weight) if layer.read(mask) == label)
            output |= mask << start
        return output

    def decode(self, word):
        self.check_word(word, self.output_weight)
        data = length = 0
        for (_, b), piece in zip(self.blocks, self.split(word)):
            layer = self.layers.get((b, piece.bit_count()))
            if layer:
                data = (data << layer.bits) | layer.read(piece)
                length += layer.bits
        if length < self.bits:
            return data << (self.bits - length)
        return data >> (length - self.bits)


def check(code, states):
    state_count = round_trips = 0
    for state in states:
        for message in range(1 << code.bits):
            word = code.encode(state, message)
            assert word & state == word and word.bit_count() == code.output_weight
            assert code.decode(word) == message
            round_trips += 1
        state_count += 1
    return state_count, round_trips


if __name__ == "__main__":
    for n, s, w, limit in [(24, 22, 11, 12), (25, 24, 10, 12), (28, 26, 14, 14)]:
        code = StrongWOM(n, s, w, limit)
        print(n, s, w, 'message bits', code.bits, 'states and round trips',
              check(code, subsets((1 << n) - 1, s)))

    for params in [(5, 0, 0), (6, 4, 0), (7, 4, 4)]:
        endpoint = StrongWOM(*params)
        assert endpoint.bits == 0
        check(endpoint, subsets((1 << endpoint.n) - 1, endpoint.state_weight))
    print('endpoint checks passed')

    # Use the theorem's logarithmic block length on clustered and dispersed states.
    large = StrongWOM(1024, 1000, 500)
    full = (1 << large.n) - 1
    states = [(1 << 1000) - 1, full ^ ((1 << 24) - 1),
              full ^ sum(1 << (43 * i) for i in range(24))]
    messages = {0, 1, (1 << large.bits) - 1, sum(1 << i for i in range(0, large.bits, 2))}
    assert large.bits > 2
    for state in states:
        for message in messages:
            word = large.encode(state, message)
            assert word & state == word and word.bit_count() == large.output_weight
            assert large.decode(word) == message
    assert large.decode((1 << large.output_weight) - 1) < 1 << large.bits
    print(f'default block length: {large.bits} bits, {len(states)*len(messages)} round trips')

