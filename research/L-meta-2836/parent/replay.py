"""Check the parent and B using the upstream project libraries and their original modules."""
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent


def main():
    upstream = ("L_meta_2904", "L_meta_1922", "L_meta_2960")
    sources = Path("PEqualNP/Outside")
    if not all((sources / f"{module}.lean").is_file() for module in upstream):
        raise SystemExit("Run from the upstream lean/ directory at a revision containing L-meta-2960.")
    environment = dict(os.environ, LEAN_NUM_THREADS="1")
    for module in upstream:
        subprocess.run(["lake", "build", f"PEqualNP.Outside.{module}"], env=environment, check=True)

    def lake_env(*arguments):
        return subprocess.check_output(["lake", "env", *arguments], env=environment, text=True).strip()

    base_path = lake_env("printenv", "LEAN_PATH")
    compiler = lake_env("which", "lean")
    pins = RESEARCH / "triple" / "pinning"
    monotone = RESEARCH / "monotone"
    ordered_sources = [
        RESEARCH / "triple" / "Restrictions.lean",
        *(pins / f"{name}.lean" for name in (
            "PinOne", "PinTwo", "PairPins", "CheckedPinTwo", "CheckedPinTwoCtor",
            "Theta2960Core", "CheckedThetaBound", "SignedSeven",
        )),
        *(monotone / f"{name}.lean" for name in ("MonotoneTransport", "MonotoneExact", "CheckedMonotone")),
        HERE / "AcceptedReduction.lean",
        HERE / "ResearchConclusions.lean",
    ]
    with tempfile.TemporaryDirectory() as build:
        environment["LEAN_PATH"] = build + os.pathsep + base_path
        for source in ordered_sources:
            output = Path(build) / source.with_suffix(".olean").name
            subprocess.run(
                [compiler, "-j1", "-R", ".", "-o", str(output), source.name],
                cwd=source.parent, env=environment, check=True,
            )


if __name__ == "__main__":
    main()
