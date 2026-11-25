"""Regenerate the finite certificate and replay it with this checkout's Lean kernel."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import shutil
import subprocess
import sys

source = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--project', type=Path, help="path to the repository's lean directory")
parser.add_argument('--build-dir', type=Path)
parser.add_argument('--jobs', type=int, default=2)
parser.add_argument('--reuse', action='store_true', help='reuse up-to-date local Lean modules from this build directory')
args = parser.parse_args()
if args.jobs < 1:
    parser.error('--jobs must be positive')
if args.project is None:
    root = next((p for p in source.parents if (p / 'lean' / 'lean-toolchain').is_file()), None)
    if root is None:
        parser.error('cannot locate project; set --project')
    args.project = root / 'lean'
project = args.project.resolve()
work = (args.build_dir or project / '.lake' / 'build' / 'cover-four-case15-partial').resolve()
work.mkdir(parents=True, exist_ok=True)

scripts = ('certify94.py', 'index94.py', 'emit94.py')
graphs = source.parent
bridge_modules = ('Equivalence', 'ResidualGraphs', 'ResidualThetas',
                  'CofactorCore15', 'FalseCofactor15', 'PartialSamples15')
bridge_sources = [graphs.parent / 'Equivalence.lean',
                  *(graphs / (name + '.lean') for name in bridge_modules[1:])]
for path in [*source.glob('*.lean'), *(source / name for name in scripts), *bridge_sources]:
    dest = work / path.name
    if not dest.is_file() or dest.read_bytes() != path.read_bytes():
        shutil.copyfile(path, dest)
for name in scripts:
    subprocess.run([sys.executable, work / name], cwd=work, check=True)

subprocess.run(['lake', 'build', '-q', 'PEqualNP.Defs.MetaComplexityLgpMono',
                'PEqualNP.Outside.L_meta_615', 'PEqualNP.MetaComplexity.Helpers.PermInputs'],
               cwd=project, check=True)
def lake_env(*cmd):
    return subprocess.check_output(['lake', 'env', *cmd], cwd=project, text=True).strip()

env = dict(os.environ, LEAN_PATH=str(work) + os.pathsep + lake_env('printenv', 'LEAN_PATH'))
lean = Path(lake_env('lean', '--print-prefix')) / 'bin' / 'lean'
search_paths = [project / p for p in env['LEAN_PATH'].split(os.pathsep)]

def check(module, force=False):
    path = work.joinpath(*module.split('.')).with_suffix('.lean')
    output = path.with_suffix('.olean')
    if args.reuse and not force and output.is_file():
        imports = [line.split()[1] for line in path.read_text().splitlines() if line.startswith('import ')]
        deps = []
        for name in imports:
            relative = Path(*name.split('.')).with_suffix('.olean')
            dep = next((p / relative for p in search_paths
                        if (p / relative).is_file()), None)
            if dep is not None:
                deps.append(dep)
        if len(deps) == len(imports) and output.stat().st_mtime_ns >= max(
                p.stat().st_mtime_ns for p in [lean, path, *deps]):
            return ''
    result = subprocess.run([lean, '-j', '1', '-R', work, '-o', output, path],
                            cwd=project, env=env, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f'{module} failed\n{result.stdout}{result.stderr}')
    return result.stdout + result.stderr

for module in ('Live', 'Checker', 'Packing', 'Node94', 'Extract15'):
    check(module)
with ThreadPoolExecutor(max_workers=args.jobs) as pool:
    for level in range(4, 12):
        shards = sorted(p.stem for p in (work / 'Case15').glob(f'L{level}B*.lean'))
        if not shards:
            raise RuntimeError(f'Missing certificates at level {level}')
        list(pool.map(check, ('Case15.' + s for s in shards)))
        print(f'Checked {len(shards)} Lean modules at budget {level}.', flush=True)

def audit(module, declaration):
    log = check(module, force=True)
    print(log, end='')
    expected = f"'{declaration}' depends on axioms: [propext, Classical.choice, Quot.sound]"
    if expected not in log.splitlines():
        raise RuntimeError(f'Missing expected axiom audit for {declaration}')

audit('Partial15', 'VertexPeel.CoverFour.Case15Partial.lower')
for name in bridge_modules:
    if name == 'FalseCofactor15':
        audit(name, 'VertexPeel.CoverFourResidual.falseCofactor15')
    else:
        check(name)
print('Checked the sampled lower bound, row-15 cofactors and sample assignments.')
