"""Check every successor of a supplied frontier, in ascending budget order."""
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from probe_data import generate


def main():
    p = json.loads((HERE.parent/'probe29.json').read_text())
    assert p == generate()
    positive, negative = p['positives'], p['negatives']
    num_positive, num_negative = len(positive), len(negative)
    positions = num_positive + num_negative
    full = (1 << positions)-1
    all_cells = (1 << (num_positive*num_negative))-1
    assert all(any(row ^ (1<<i) in negative for row in positive) for i in range(7))
    goal = p['positive_mask'] ^ full

    def canon(word):
        return full ^ word if word & 1 else word

    def exchange(word,mask,distance):
        difference = mask & (word ^ (word>>distance))
        return word ^ difference ^ (difference<<distance)

    @lru_cache(maxsize=32768)
    def images(word):
        return [canon(exchange(exchange(word,m,1),n,2)) for m,n in p['swap_masks']]

    def normalized(wires):
        return min(tuple(sorted(image)) for image in zip(*(images(word) for word in wires)))

    @lru_cache(maxsize=32768)
    def cover(word):
        fwd, reverse = 0,0
        for pi in range(num_positive):
            for ni in range(num_negative):
                cell = 1 << (num_negative*pi + ni)
                in_positive = (word >> pi) & 1
                in_negative = (word >> (num_positive+ni)) & 1
                if in_positive > in_negative:
                    fwd |= cell
                if in_positive < in_negative:
                    reverse |= cell
        return fwd | reverse, fwd, reverse

    @lru_cache(maxsize=32768)
    def rectangle(cells):
        rows,cols = 0,0
        while cells:
            bit = cells & -cells
            row,col = divmod(bit.bit_length()-1,num_negative)
            rows |= 1 << row
            cols |= 1 << col
            cells ^= bit
        return sum(cols << (i*num_negative) for i in range(num_positive) if rows>>i&1)

    @lru_cache(maxsize=110000)
    def directly_excluded(wires, budget):
        if len(wires) > budget+1:
            return True
        if len(wires) == 1:
            return wires[0] != goal
        cov = [cover(word) for word in wires]
        once,many = 0,0
        for domain,_,_ in cov:
            many |= once & domain
            once |= domain
        if once != all_cells:
            return True
        if len(wires) != budget+1:
            return False
        owned = 0
        private = once & ~many
        for domain,yes,no in cov:
            forced = private & domain
            if forced & yes and forced & no:
                return True
            product = rectangle(forced)
            if owned & product:
                return True
            owned |= product
        return False

    def decode(code):
        words = []
        while code > 1:
            words.append(code & full)
            code >>= positions
        assert code == 1
        return tuple(reversed(words))

    def successors(state):
        for i,j in combinations(range(len(state)),2):
            a,b = state[i],state[j]
            rest = state[:i] + state[i+1:j] + state[j+1:]
            for x in (a,a^full):
                for y in (b,b^full):
                    new = canon(x&y)
                    if not new or new in state:
                        continue
                    for keep in ((),(a,),(b,),(a,b)):
                        yield tuple(sorted((*rest,*keep,new)))

    checked = {}
    transitions = 0
    for line in (HERE/'frontier.txt').read_text().splitlines():
        budget_text,*codes = line.split()
        budget = int(budget_text)
        assert not checked or max(checked) < budget
        states = {decode(int(code,16)) for code in codes}
        assert len(codes) == len(states)
        for state in states:
            assert state == normalized(state) and len(set(state)) == len(state)
            assert all(word and not word & 1 for word in state)
            assert not directly_excluded(state,budget)
            assert len(state)>1
            for child in successors(state):
                transitions += 1
                if directly_excluded(child,budget-1):
                    continue
                assert normalized(child) in checked.get(budget-1,set()), (budget,state,child)
        checked[budget] = states
    initial = normalized(tuple(canon(word) for word in p['raw']))
    assert initial in checked[10]
    print(f"Closed {sum(map(len,checked.values()))} supplied states, including the initial state.")
    print(f"Checked {transitions} unfiltered nondegenerate transitions.")


if __name__ == '__main__':
    main()
