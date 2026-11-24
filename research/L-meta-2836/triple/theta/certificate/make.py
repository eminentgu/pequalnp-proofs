"""Generate a descending certificate of finite signed theta states."""
from collections import defaultdict
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from probe_data import generate
from rows import solve

WIDTH = 29


def encode(state):
    result = 1
    for word in state:
        result = (result << WIDTH) | word
    return result


def main():
    bank = generate()
    expanded = defaultdict(set)
    result = solve(bank['positives'], bank['negatives'], swap_masks=bank['swap_masks'],
                   on_expand=lambda remaining,state: expanded[remaining].add(encode(state)))
    assert result['possible'] is False
    with Path(__file__).with_name('frontier.txt').open('w') as out:
        for remaining, states in sorted(expanded.items()):
            print(remaining, *(format(state,'x') for state in sorted(states)), file=out)


if __name__ == '__main__':
    main()
