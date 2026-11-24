"""Check the published 29-row bank, the lower bound and its matching upper bound."""
import json
from pathlib import Path

import graph
from probe_data import generate
from rows import solve


def main():
    supplied = json.loads(Path(__file__).with_name("probe29.json").read_text())
    assert supplied == generate()
    result = solve(supplied["positives"],supplied["negatives"],swap_masks=supplied["swap_masks"])
    assert result == dict(possible=False, positive=16, negative=13, normal=1616, calls=23484,
                          tight=21868, by_budget={5:4,6:189,7:836,8:558,9:28,10:1})
    for row in range(128):
        a,b,c,d,e,f,g = [(row >> i) & 1 for i in range(7)]
        formula = (a & (b|e)) | (b & (c|f)) | (d & f) | (g & (c|e|d))
        assert bool(formula) == (row in graph.POS)
    print("All 128 rows agree with the 11-gate upper bound.",flush=True)


if __name__ == "__main__":
    main()
