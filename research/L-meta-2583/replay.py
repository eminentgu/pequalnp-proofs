"""Rebuild the upstream dependencies and kernel-check the local research modules."""
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent

UPSTREAM = ("L_meta_1955", "L_meta_2237", "L_meta_2988", "L_meta_1483", "L_meta_1983")
SOURCES = (
    "IncidenceReadPairs", "LineStarUpper", "lower/PlaneReadOne", "Threshold",
    "lower/UnrestrictedRange", "fano/Fano27", "fano/FanoBounds", "fano/FanoReadOne",
)


def main():
    if not Path("PEqualNP/Outside").is_dir():
        raise SystemExit("Run from the project's lean/ directory.")
    environment = dict(os.environ, LEAN_NUM_THREADS="1")
    for module in UPSTREAM:
        subprocess.run(["lake", "build", f"PEqualNP.Outside.{module}"], env=environment, check=True)

    def lake_env(*args):
        return subprocess.check_output(["lake", "env", *args], env=environment, text=True).strip()

    compiler = lake_env("which", "lean")
    base_path = lake_env("printenv", "LEAN_PATH")
    with tempfile.TemporaryDirectory() as build:
        environment["LEAN_PATH"] = build + os.pathsep + base_path
        for name in SOURCES:
            source = HERE / f"{name}.lean"
            output = Path(build) / source.with_suffix(".olean").name
            subprocess.run([compiler, "-j1", "-R", ".", "-o", str(output), source.name],
                           cwd=source.parent, env=environment, check=True)


if __name__ == "__main__":
    main()
