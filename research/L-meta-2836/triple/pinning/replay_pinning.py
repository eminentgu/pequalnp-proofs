"""Check the pinning modules inside the upstream Lean project's lake environment."""
from os import environ, pathsep
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
UPSTREAM = Path("PEqualNP/Outside/L_meta_2904.lean")


def subset(source, start, stop):
    begin = source.index(start)
    return source[begin:source.index(stop, begin)]


def main():
    if not UPSTREAM.exists():
        raise SystemExit("Run from the upstream lean/ directory using lake env python3.")
    source = UPSTREAM.read_text()
    # These intervals preserve the published definitions and proofs byte-for-byte.
    # They only omit later circuit lower bound searches and unused helper lemmas.
    upstream = ("import PEqualNP.Defs.MetaComplexity\n\n"
                + subset(source, "namespace PEqualNP.Outside", "def gateSupp")
                + subset(source, "inductive Stat : Type", "theorem elim_len (")
                + subset(source, "theorem Stat.valid_mono", "def initStats")
                + "\nend PEqualNP.Outside.L_meta_2904\n")
    with TemporaryDirectory() as temp:
        build = Path(temp)
        old = build / UPSTREAM
        old.parent.mkdir(parents=True)
        old.write_text(upstream)
        definitions = Path(".lake/build/lib/lean/PEqualNP/Defs").resolve()
        if not (definitions / "MetaComplexity.olean").exists():
            raise SystemExit("First run lake build PEqualNP.Defs.MetaComplexity.")
        (build / "PEqualNP" / "Defs").symlink_to(definitions, target_is_directory=True)
        env = environ.copy()
        env["LEAN_NUM_THREADS"] = "1"
        env["LEAN_PATH"] = str(build) + pathsep + env.get("LEAN_PATH", "")
        for file in (old, HERE.parent / "Restrictions.lean", HERE / "PinOne.lean", HERE / "PinTwo.lean", HERE / "PairPins.lean", HERE / "CheckedPinTwo.lean", HERE / "CheckedPinTwoCtor.lean"):
            if file == old:
                directory = build
                relative = UPSTREAM
            else:
                directory = file.parent
                relative = Path(file.name)
            output = build / relative.with_suffix(".olean")
            run(["lean", "-j1", "-R", ".", "-o", str(output), str(relative)],
                check=True, cwd=directory, env=env)


if __name__ == "__main__":
    main()
