"""Regenerate the canonical graph classification witnesses and check their proofs in Lean."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

source = Path(__file__).resolve().parent
cover = source.parent
research = cover.parent
default_project = research.parents[1] / 'lean'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--project', type=Path, default=default_project)
parser.add_argument('--build-dir', type=Path)
parser.add_argument('--jobs', type=int, default=2)
args = parser.parse_args()
if args.jobs < 1:
    parser.error('--jobs must be positive')
project = args.project.resolve()
work = (args.build_dir or project / '.lake/build/cover-four-classes').resolve()
work.mkdir(exist_ok=True, parents=True)
for path in (research/'Equivalence.lean', cover/'Mask4.lean', cover/'ResidualGraphs.lean',
             cover/'Canonical186.lean', source/'ExitCore.lean', source/'CriticalExit.lean'):
    shutil.copyfile(path, work/path.name)
subprocess.run([sys.executable, source/'generate.py', work], check=True)
subprocess.run(['lake','build','-q','PEqualNP.MetaComplexity.Helpers.PermInputs',
                'PEqualNP.MetaComplexity.Helpers.LocGraph', 'PEqualNP.Defs'], cwd=project, check=True)

def lake(*cmd):
    return subprocess.check_output(['lake','env',*cmd], cwd=project, text=True).strip()

lean = Path(lake('lean','--print-prefix')) / 'bin/lean'
env = dict(os.environ, LEAN_PATH=str(work) + os.pathsep + lake('printenv','LEAN_PATH'))

def check(name):
    log = work / f'{name}.log'
    with log.open('w') as fp:
        result = subprocess.run([lean,'-j1','-R',work,'-o',work/f'{name}.olean',work/f'{name}.lean'],
                                stdout=fp,stderr=subprocess.STDOUT, env=env,cwd=project)
    if result.returncode:
        raise RuntimeError(f'{name} failed\n{log.read_text()}')

for name in ('Equivalence','ResidualGraphs','Mask4','Canonical186','ExitCore','CriticalExit'):
    check(name)
started = time.monotonic()
shards = sorted(work.glob('Exits186_*.lean'), key=lambda p:int(p.stem.split('_')[1]))
with ThreadPoolExecutor(max_workers=args.jobs) as pool:
    for i, _ in enumerate(pool.map(check, [p.stem for p in shards]), 1):
        print(f'Checked batch {i} of {len(shards)} in {time.monotonic()-started:.1f}s total',flush=True)
check('Classified186')
audit = (work/'Classified186.log').read_text()
expected = "'VertexPeel.CoverFourClass.classified' depends on axioms: [propext, Classical.choice, Quot.sound]"
if expected not in audit.splitlines():
    raise RuntimeError(f'Unexpected audit in {work/"Classified186.log"}')
print(expected)
