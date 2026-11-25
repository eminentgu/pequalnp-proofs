"""Regenerate the search table and check the exclusion and the counterexample with Lean."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import subprocess
import sys
import time

source = Path(__file__).resolve().parent
repository = source.parents[2]
project = repository / 'lean'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--jobs',type=int,default=2,help='number of parallel Lean processes')
parser.add_argument('--build-dir',type=Path,default=project/'.lake'/'build'/'finite-witness-1774')
args = parser.parse_args()
if args.jobs < 1:
    parser.error('--jobs must be positive')
work = args.build_dir.resolve()
work.mkdir(exist_ok=True,parents=True)
inputs = list(source.glob('*.lean')) + [source/name for name in ('certify94.py','index94.py','emit94.py')]
for path in inputs:
    dest = work/path.name
    if not dest.is_file() or dest.read_bytes() != path.read_bytes():
        dest.write_bytes(path.read_bytes())
for name in ('certify94.py','index94.py','emit94.py'):
    subprocess.run([sys.executable,str(work/name)],cwd=work,check=True)

target='PEqualNP.Research.L_meta_1774.WitnessNine'
subprocess.run(['lake','build','-q',target],cwd=project,check=True)
env=os.environ.copy()
env['LEAN_PATH']=str(work)+os.pathsep+subprocess.check_output(
    ['lake','env','printenv','LEAN_PATH'],cwd=project,text=True).strip()
prefix=subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=project,text=True).strip()
lean=Path(prefix)/'bin'/'lean'

def check(path):
    obj=path.with_suffix('.olean')
    dependencies=[]
    for line in path.read_text().splitlines():
        if line.startswith('import '):
            module=line[7:].strip()
            local=work.joinpath(*module.split('.')).with_suffix('.olean')
            dependencies.append(local if local.is_file() else project/'.lake'/'build'/'lib'/'lean'/local.relative_to(work))
    timestamps=[path.stat().st_mtime,*(f.stat().st_mtime for f in dependencies if f.is_file())]
    if obj.is_file() and obj.stat().st_mtime>=max(timestamps):
        return
    log=path.with_suffix('.log')
    with log.open('w') as stream:
        run=subprocess.run([lean,'-j','1','-R',work,'-o',obj,path],env=env,cwd=project,stdout=stream,stderr=subprocess.STDOUT)
    if run.returncode:
        raise RuntimeError(f'{path.name} failed. See {log}\n{log.read_text()[:850]}')

for module in ('Live','Checker','Packing','Node94','Extract','WitnessBridge','WitnessDescent','TopWitness'):
    check(work/(module+'.lean'))
with ThreadPoolExecutor(args.jobs) as pool:
    for remaining in range(3,12):
        batch=sorted((work/'Case94').glob(f'L{remaining}B*.lean'),key=lambda p:int(p.stem.split('B')[1]))
        if not batch:
            raise RuntimeError(f'Missing state proofs at budget {remaining}')
        start=time.monotonic()
        for _ in pool.map(check,batch):
            pass
        print(f'Budget {remaining}: {len(batch)} proof modules checked ({time.monotonic()-start:.1f}s).',flush=True)
for module in ('Conclusion',):
    check(work/(module+'.lean'))
    audit=(work/(module+'.log')).read_text()
    print(audit,end='')
    declarations=('noSmall','lower','minimum','negates4848','graphDescent','topFormMinimum')
    for name in declarations:
        suffix="."+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]"
        if not any(suffix in line for line in audit.splitlines()):
            raise RuntimeError(f'Missing or unexpected axiom audit for {name}')
