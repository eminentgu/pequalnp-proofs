#!/usr/bin/env python3
"""Build the complete cover-four proof and audit the four public statements."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import graphlib
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


COVER = Path(__file__).resolve().parent
RESEARCH = COVER.parent
TARGET = "CoverFour"
EXPECTED = {
    "VertexPeel.CoverFour." + name
    for name in (
        "numerical_four",
        "ownership_at_most_four",
        "vertex_at_most_four",
        "bipartite_vertex_at_most_four",
    )
}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def imports(path):
    # Lean's research modules place each import in the header. Ignore both
    # nested block comments and line comments when reading this header.
    header = []
    depth = 0
    for line in path.read_text().splitlines():
        tokens = re.split(r"(/-|-/|--)", line)
        visible = []
        for token in tokens:
            if token == "/-":
                depth += 1
            elif token == "-/" and depth:
                depth -= 1
            elif token == "--" and not depth:
                break
            elif not depth:
                visible.append(token)
        line = "".join(visible).strip()
        if not line or line in ("module", "prelude"):
            continue
        match = re.fullmatch(r"(?:(?:public|meta|all)\s+)*import\s+([\w.\s]+)", line)
        if not match:
            break
        header.extend(match.group(1).split())
    return tuple(header)


def generate(work):
    partial = work / "case15-sources"
    classes = work / "class186-sources"
    partial.mkdir(parents=True, exist_ok=True)
    classes.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    for name in ("certify94.py", "index94.py", "emit94.py"):
        shutil.copyfile(COVER / "partial15" / name, partial / name)
        subprocess.run([sys.executable, partial / name], cwd=partial, env=env, check=True)
    subprocess.run([sys.executable, COVER / "class186/generate.py", classes], env=env, check=True)
    return partial, classes


def sources_for(partial, classes):
    sources = {}
    for root in (RESEARCH, COVER, COVER / "partial15", COVER / "class186", classes, partial):
        pattern = "Case15/*.lean" if root == partial else "*.lean"
        for path in root.glob(pattern):
            name = ".".join(path.relative_to(root).with_suffix("").parts)
            if name in sources:
                raise ValueError(f"Two sources for {name}: {path} and {sources[name][0]}")
            sources[name] = (path, root)
    return sources


def closure(sources):
    local, external = {}, {}

    def visit(name):
        if name in local:
            return
        deps = imports(sources[name][0])
        local[name] = [d for d in deps if d in sources]
        external[name] = [d for d in deps if d not in sources]
        for child in local[name]:
            visit(child)

    visit(TARGET)
    return local, external


def certificate_module(name):
    return name.startswith(("Case15.", "Exits186_"))


def audit(text):
    found = {}
    pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    for name, deps in re.findall(pattern, text):
        if name in EXPECTED:
            found[name] = {a.strip() for a in deps.split(",") if a.strip()}
    if found.keys() != EXPECTED:
        raise RuntimeError(f"Missing audit entries: {sorted(EXPECTED - found.keys())}")
    for name, axioms in sorted(found.items()):
        if not axioms <= STANDARD_AXIOMS:
            raise RuntimeError(f"Unexpected axioms for {name}: {sorted(axioms - STANDARD_AXIOMS)}")
        print(f"{name}: {', '.join(sorted(axioms))}", flush=True)


def verify(project, work, jobs, certificate_caches):
    if not (COVER / "CoverFour.lean").is_file():
        raise FileNotFoundError(COVER / "CoverFour.lean")
    partial, classes = generate(work)
    sources = sources_for(partial, classes)
    local, external = closure(sources)
    external_names = sorted({d for deps in external.values() for d in deps})
    print(f"Building the Lake dependencies of {len(local)} research modules.", flush=True)
    if external_names:
        subprocess.run(["lake", "build", "-q", *external_names], cwd=project, check=True)

    def lake(*cmd):
        return subprocess.check_output(["lake", "env", *cmd], cwd=project, text=True).strip()

    lean = Path(lake("lean", "--print-prefix")) / "bin/lean"
    lake_paths = lake("printenv", "LEAN_PATH")
    roots = [project / p for p in lake_paths.split(os.pathsep)]
    objects = work / "objects"
    logs = work / "logs"
    objects.mkdir(exist_ok=True)
    logs.mkdir(exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(objects) + os.pathsep + lake_paths)
    version = subprocess.check_output([lean, "--version"], text=True).strip()
    external_signatures = {}
    for name in external_names:
        rel = Path(*name.split(".")).with_suffix(".olean")
        obj = next((root / rel for root in roots if (root / rel).is_file()), None)
        if obj is None:
            raise FileNotFoundError(f"Lake did not provide {name}")
        external_signatures[name] = digest(obj)
    source_hashes = {n: digest(sources[n][0]) for n in local}
    keys = {}
    order = tuple(graphlib.TopologicalSorter(local).static_order())
    for name in order:
        parts = ([version, name, source_hashes[name]] + [keys[d] for d in local[name]]
                 + [external_signatures[d] for d in external[name]])
        keys[name] = hashlib.sha256("\0".join(parts).encode()).hexdigest()

    # Read-only seeds refer to prior successful local runs of the two standalone
    # certificate checkers. Match all local sources in their dependency closure.
    seed_ok = {}
    for cache in certificate_caches:
        for name in order:
            rel = Path(*name.split("."))
            src = cache / rel.with_suffix(".lean")
            obj = cache / rel.with_suffix(".olean")
            seed_ok[cache, name] = (src.is_file() and obj.is_file()
                                    and obj.stat().st_mtime_ns >= src.stat().st_mtime_ns
                                    and digest(src) == source_hashes[name]
                                    and all(seed_ok[cache, child] for child in local[name]))

    def build(name):
        src, root = sources[name]
        rel = Path(*name.split(".")).with_suffix(".olean")
        obj = objects / rel
        obj.parent.mkdir(parents=True, exist_ok=True)
        stamp = obj.with_suffix(".json")
        if name != TARGET and obj.is_file() and stamp.is_file():
            try:
                state = json.loads(stamp.read_text())
            except ValueError:
                state = {}
            if (isinstance(state, dict) and state.get("inputs") == keys[name]
                    and state.get("object") == digest(obj)):
                return "reused"
        seed = next((c / rel for c in certificate_caches if certificate_module(name)
                     and seed_ok[c, name]), None)
        if seed:
            shutil.copyfile(seed, obj)
        else:
            log = logs / (name + ".log")
            with tempfile.TemporaryDirectory(dir=obj.parent) as temp:
                output = Path(temp) / obj.name
                with log.open("w") as stream:
                    run = subprocess.run([lean, "-j1", "-R", root, "-o", output, src],
                                         cwd=project, env=env, stdout=stream, stderr=subprocess.STDOUT)
                if run.returncode:
                    raise RuntimeError(f"{name} failed ({run.returncode})\n{log.read_text()[-6000:]}")
                if name == TARGET:
                    audit(log.read_text())
                output.replace(obj)
        stamp.write_text(json.dumps({"inputs": keys[name], "object": digest(obj)}))
        return "certificate" if seed else "compiled"

    counts = dict(compiled=0, certificate=0, reused=0)
    dag = graphlib.TopologicalSorter(local)
    dag.prepare()
    pending = {}
    completed = 0
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while dag.is_active():
            for name in dag.get_ready():
                pending[pool.submit(build, name)] = name
            finished, _ = wait(pending, return_when=FIRST_COMPLETED)
            for future in finished:
                counts[future.result()] += 1
                dag.done(pending.pop(future))
            completed += len(finished)
            if completed == len(local) or completed // 20 != (completed - len(finished)) // 20:
                print(f"Checked {completed}/{len(local)} research modules.", flush=True)
    print(f"Completed with {counts['compiled']} compiled, {counts['reused']} reused, "
          f"and {counts['certificate']} matched certificate objects.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=RESEARCH.parents[1] / "lean")
    parser.add_argument("--build-dir", type=Path, help="persistent local build directory")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--certificate-cache", type=Path, action="append", default=[],
                        help="trusted build from a successful partial15 or class186 verification (repeatable)")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    project = args.project.resolve()
    work = (args.build_dir or project / ".lake/build/cover-four-all").resolve()
    work.mkdir(parents=True, exist_ok=True)
    verify(project, work, args.jobs, [p.resolve() for p in args.certificate_cache])


if __name__ == "__main__":
    main()
