"""Specialize L-meta-2466's 34-gate counting estimate to the sparse L-meta-2990 promise."""
from pathlib import Path
import argparse


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("upstream", type=Path, help="directory containing the upstream Outside modules")
    cli.add_argument("output", type=Path, help="output SharpTwice.lean")
    args = cli.parse_args()
    fine = (args.upstream / "L_meta_2466.lean").read_text()
    sparse = (args.upstream / "L_meta_2673.lean").read_text()
    proof = sparse[sparse.index("private lemma card_points_le"):sparse.index("end Degrees")]
    point = fine.index("end Degrees")
    fine = fine[:point] + proof + fine[point:]
    point = fine.index("private theorem twice_sharp_bound")
    original = fine[point:fine.index("end SharpCounting",point)]
    old_start = original.index("    (hFun :")
    old_end = original.index("    (twiceEdges",old_start)
    sig = sparse[sparse.index("private lemma hom_output_safe2"):]
    sparse_premise = sig[sig.index("    (hS :"):sig.index("    {a b :")]
    replacement = (original[:old_start] + sparse_premise.rstrip() + " :\n" + original[old_end:])
    replacement = replacement.replace("private theorem twice_sharp_bound", "theorem sparseTwice")
    for sub in ("mixed_sound","pure_sound"):
        old = f"hom_output_safe I hAO hFun ({sub} hAO valid h.1 h.2)"
        assert old in replacement
        replacement = replacement.replace(old, f"hom_output_safe2 I hAO hS ({sub} hAO valid h.1 h.2) le_rfl le_rfl")
    text = (fine[:point] + replacement + "end SharpCounting\n\nend PEqualNP.Outside.L_meta_2466\n\n"
            "#print axioms PEqualNP.Outside.L_meta_2466.sparseTwice\n")
    text = text.replace("PEqualNP.Outside.L_meta_2466", "IncidenceTwice2990")
    args.output.write_text(text)


if __name__ == "__main__":
    main()
