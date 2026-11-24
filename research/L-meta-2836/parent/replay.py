"""Check the parent and B using the upstream project libraries and their original modules."""
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent


def main():
    root = Path.cwd()
    upstream = ("L_meta_2904","L_meta_1922","L_meta_2960")
    if not all((root / "PEqualNP/Outside" / (m+".lean")).is_file() for m in upstream):
        raise SystemExit("Run from the upstream lean/ directory at a revision containing L-meta-2960.")
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    for module in upstream:
        subprocess.run(["lake","build","PEqualNP.Outside."+module],env=env,check=True)
    base = subprocess.check_output(["lake","env","printenv","LEAN_PATH"],env=env,text=True).strip()
    compiler = subprocess.check_output(["lake","env","which","lean"],env=env,text=True).strip()
    pins = RESEARCH/"triple"/"pinning"
    mono = RESEARCH/"monotone"
    sources = [
        RESEARCH/"triple"/"Restrictions.lean",
        *(pins/(m+".lean") for m in ("PinOne","PinTwo","PairPins","CheckedPinTwo","CheckedPinTwoCtor",
                                      "Theta2960Core","CheckedThetaBound")),
        *(mono/(m+".lean") for m in ("MonotoneTransport","MonotoneExact","CheckedMonotone")),
        HERE/"AcceptedReduction.lean",HERE/"ResearchConclusions.lean",
    ]
    with tempfile.TemporaryDirectory() as build:
        env["LEAN_PATH"] = build + os.pathsep + base
        for source in sources:
            output = Path(build)/source.with_suffix(".olean").name
            subprocess.run([compiler,"-j1","-R",".","-o",str(output),source.name],
                           cwd=source.parent,env=env,check=True)


if __name__ == "__main__":
    main()
