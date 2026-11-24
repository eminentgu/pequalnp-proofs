"""Rebuild the upstream dependencies and kernel-check the local research modules."""
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent

UPSTREAM = ("L_meta_1955", "L_meta_2237", "L_meta_1892", "L_meta_1483", "L_meta_1983",
            "L_meta_3008", "R_meta_4387_184")
SOURCES = (
    "Normalize", "Incomparable", "UpperWitness", "LastAnd", "RootSupport", "SmallOperand", "TerminalCut",
    "../L-meta-2583/lower/PlaneReadOne", "../L-meta-2583/lower/CleanAnd",
    "../L-meta-2583/fano/Fano27", "../L-meta-2583/fano/FanoBounds",
    "PhysicalChain", "PhysicalHeawood", "EssentialRaw", "CheckedPhysical", "Conditional4387",
)


def main():
    if not Path("PEqualNP/Outside").is_dir():
        raise SystemExit("Run from the project's lean/ directory.")
    environment = dict(os.environ, LEAN_NUM_THREADS="1")
    subprocess.run(["lake", "build", "PEqualNP.Defs"], env=environment, check=True)

    def lake_env(*args):
        return subprocess.check_output(["lake", "env", *args], env=environment, text=True).strip()

    compiler = lake_env("which", "lean")
    base_path = lake_env("printenv", "LEAN_PATH")
    with tempfile.TemporaryDirectory() as build:
        environment["LEAN_PATH"] = build + os.pathsep + base_path
        upstream_dir = Path(build) / "PEqualNP" / "Outside"
        upstream_dir.mkdir(parents=True)
        # Lean resolves a namespace from the first matching directory on LEAN_PATH.
        # Expose the installed project modules alongside the isolated Outside directory.
        project_modules = Path(".lake/build/lib/lean/PEqualNP").resolve()
        for item in project_modules.iterdir():
            if item.name != "Outside":
                (upstream_dir.parent / item.name).symlink_to(item, target_is_directory=item.is_dir())
        for module in UPSTREAM:
            source = Path("PEqualNP/Outside") / f"{module}.lean"
            subprocess.run([compiler, "-j1", "-R", ".", "-o", str(upstream_dir / f"{module}.olean"),
                            str(source)], env=environment, check=True)
        for name in SOURCES:
            source = HERE / f"{name}.lean"
            output = Path(build) / source.with_suffix(".olean").name
            subprocess.run([compiler, "-j1", "-R", ".", "-o", str(output), source.name],
                           cwd=source.parent, env=environment, check=True)


if __name__ == "__main__":
    main()
