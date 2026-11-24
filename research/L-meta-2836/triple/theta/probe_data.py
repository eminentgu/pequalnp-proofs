"""Build the signed theta bank and its two-stage bit permutations."""
from itertools import permutations
import json

from rows import rows, theta


def image(row, permutation):
    return sum((row >> i & 1) << permutation[i] for i in range(7))


def generate():
    positive, negative = rows("tiny")
    group = [perm for perm in permutations(range(7))
             if all(image(edge, perm) in theta.MASKS for edge in theta.MASKS)]
    assert len(group) == 4 and group[0] == tuple(range(7))
    _, generator, second, both = group
    assert tuple(generator[second[i]] for i in range(7)) == both

    groups = []
    for bank in (positive, negative):
        remaining = set(bank)
        while remaining:
            row = min(remaining)
            block = list(dict.fromkeys(image(row, perm) for perm in group))
            assert len(block) in (1,2,4) and set(block) <= remaining
            remaining.difference_update(block)
            groups.append(block)
    ordered = [row for block in groups for row in block]
    assert set(ordered[:len(positive)]) == set(positive)
    full = (1 << len(ordered)) - 1

    def apply(mask, distance, value):
        differences = (value ^ (value >> distance)) & mask
        return value ^ differences ^ (differences << distance)

    masks = []
    for perm in group:
        swaps = [0,0]
        start = 0
        for block in groups:
            offset = block.index(image(block[0], perm))
            for local, row in enumerate(block):
                assert block[local ^ offset] == image(row, perm)
                for bit in range(2):
                    distance = 1 << bit
                    if (offset & distance) and not (local & distance):
                        swaps[bit] |= 1 << (start + local)
            start += len(block)
        for i, row in enumerate(ordered):
            value = apply(swaps[1],2,apply(swaps[0],1,1 << i))
            assert value == 1 << ordered.index(image(row, perm))
        masks.append(swaps)
    return dict(vertex_order=list(theta.VERTICES), positives=ordered[:len(positive)],
                negatives=ordered[len(positive):], full_mask=full,
                positive_mask=(1<<len(positive))-1,
                raw=[sum(((row >> i) & 1) << j for j,row in enumerate(ordered)) for i in range(7)],
                permutations=[list(perm) for perm in group], swap_masks=masks)


if __name__ == "__main__":
    print(json.dumps(generate(),indent=2))
