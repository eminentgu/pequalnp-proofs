"""Append the partial-read count to the published L-meta-2673 accounting argument."""
import argparse
from pathlib import Path


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("upstream", type=Path, help="upstream L_meta_2673.lean")
    cli.add_argument("output", type=Path, help="output FinalAccounting.lean")
    cli.add_argument("--coarse", action="store_true", help="self-contained 94-gate estimate using only L-meta-2673")
    args = cli.parse_args()
    original = args.upstream.read_text()
    prelude = original[:original.index("lemma main (q N")].replace(
        "PEqualNP.Outside.L_meta_2673", "Incidence2990")
    appendix = "Accounting.lean.inc" if args.coarse else "SharpAccounting.lean.inc"
    local = Path(__file__).resolve().with_name(appendix).read_text()
    attribution = "/- The read-budget machinery below is from the merged L-meta-2673 proof. -/\n"
    imports = "" if args.coarse else "import SharpTwice\n"
    args.output.write_text(imports + attribution + prelude + local
                           + "\nend Incidence2990\n\n#print axioms Incidence2990.accounting\n")


if __name__ == "__main__":
    main()
