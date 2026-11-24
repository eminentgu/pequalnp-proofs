"""Render the standalone proof of the signed B subproblem from its local modules."""
from argparse import ArgumentParser
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


def take(source, beginning, ending):
    start = source.index(beginning)
    return source[start:source.index(ending, start)].rstrip()


def body(path):
    return "\n".join(line for line in path.read_text().splitlines() if not line.startswith("import ")).strip()


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("upstream", type=Path, help="upstream PEqualNP/Outside/L_meta_2904.lean")
    parser.add_argument("output", type=Path, help="output L_<assigned-ID>.lean; determines the theorem name")
    args = parser.parse_args()
    if not re.fullmatch(r"L_[a-z0-9_]+", args.output.stem):
        parser.error("use the outside proof file name L_<assigned-ID>.lean")
    module = "PEqualNP.Outside." + args.output.stem
    upstream = args.upstream.read_text()
    uses = [
        "/- The constant-propagation definitions and their correctness proof below come from "
        "the published module PEqualNP.Outside.L_meta_2904. -/",
        take(upstream, "namespace PEqualNP.Outside.L_meta_2904", "def gateSupp"),
        take(upstream, "inductive Stat : Type", "theorem elim_len ("),
        take(upstream, "theorem Stat.valid_mono", "def initStats"),
        "end PEqualNP.Outside.L_meta_2904",
    ]
    restrictions = body(HERE.parent / "Restrictions.lean")
    uses.extend([
        take(restrictions, "namespace Triple2836", "def aux"),
        take(restrictions, "def row ", "/-- The graph outputs"),
        "end Triple2836",
        body(HERE / "PinOne.lean"),
    ])
    pins = body(HERE / "PinTwo.lean")
    uses.extend([
        take(pins, "open PEqualNP.CircuitLowerBounds", "private def original"),
        take(pins, "def pin (", "private def firstLabels"),
        take(pins, "private def constFlag", "private theorem firstTracks"),
        take(pins, "private theorem cost_le_length", "/-- The charged budget"),
        "end Triple2836",
        body(HERE / "PairPins.lean"),
    ])
    transport = body(HERE / "Theta2960Core.lean")
    signed = body(HERE / "SignedSeven.lean")
    uses.extend([
        take(transport, "open PEqualNP.CircuitLowerBounds", "/-- Apply the exact seven-vertex"),
        "end Triple2836",
        signed,
    ])
    helpers = "\n\n".join(uses).replace("PEqualNP.Outside.L_meta_2904", "Rewiring")
    helpers = helpers.replace("the published module Rewiring", "the published module PEqualNP.Outside.L_meta_2904")
    statement = take(signed, "theorem signedSeven : ", " := by\n  intro f C")
    statement = statement.removeprefix("theorem signedSeven : ")
    proof = (
        "import PEqualNP.Defs\n\n"
        f"namespace {module}\n\n{helpers}\n\nend {module}\n\n"
        "open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity\n\n"
        f"theorem {module} : {statement} :=\n  {module}.Triple2836.signedSeven\n"
    )
    args.output.write_text(proof)


if __name__ == "__main__":
    main()
