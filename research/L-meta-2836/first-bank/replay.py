"""Rebuild the five bank-A proofs from checked-in Lean and pinned public sources."""
import argparse
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from urllib.request import urlopen

HERE = Path(__file__).resolve().parent
COMMIT = '497d90c67a354aa0f43bdbf623a768e4051b8bd4'
BASE = 'research/L-meta-3561'
RAW = f'https://raw.githubusercontent.com/eminentgu/pequalnp-proofs/{COMMIT}/{BASE}'
UPSTREAM = {
    'EncodedBank': '09900e4ff7a2239777b063d198dabb086daeaeb4ee02917adaf2e59f1b4185ce',
    'SearchCore': '6ff4885034a74553b0ec3f57e499b668d16aa4906d43f351a972abded673efd3',
    'SignedReadOnceKW': '0a8d43c20e7535bc622a621d8c9dd12492bec3f9a4ecaaf23b461cf80b644077',
    'VerifiedCore': '6343c42748cdead01172e7751f2652ae71e0a69011753a118ded5691b357264f',
}
JOINED = 'bdcdcfb14c3349648a48b54a438cc85629aa2d328b6a335dbb2275bf2e9b7f49'
PROOFS = ['FirstBank', 'FirstMemo3', 'FirstCert3', 'FirstMemo2', 'FirstCert2']

def pinned(name, data, digest):
    if hashlib.sha256(data).hexdigest() != digest:
        raise ValueError(f'Public source hash mismatch for {name}')
    return data

def public_source(project, name, download):
    if not download:
        obj = f'{COMMIT}:{BASE}/{name}.lean'
        git = subprocess.run(['git','-C',str(project),'show',obj], capture_output=True)
        if git.returncode == 0:
            return pinned(name, git.stdout, UPSTREAM[name])
    with urlopen(f'{RAW}/{name}.lean', timeout=45) as response:
        return pinned(name, response.read(), UPSTREAM[name])

def prepare(project, dest, download):
    sources = {name: public_source(project,name,download) for name in UPSTREAM}
    for name in ('EncodedBank','SearchCore'):
        (dest / (name+'.lean')).write_bytes(sources[name])
    # Reproduce the exact VerifiedCore source used in the recorded Lean run.
    signed = sources['SignedReadOnceKW'].removeprefix(b'import EncodedBank\n')
    verified = sources['VerifiedCore'].removeprefix(b'import SearchCore\nimport SignedReadOnceKW\n\n')
    combined = b'import SearchCore\n' + signed + verified
    (dest/'VerifiedCore.lean').write_bytes(pinned('joined VerifiedCore',combined,JOINED))
    for unit in PROOFS:
        shutil.copyfile(HERE/(unit+'.lean'), dest/(unit+'.lean'))

def verify(project, dest):
    lake_dir = project/'lean'
    lean = subprocess.check_output(['elan','which','lean'],cwd=lake_dir,text=True).strip()
    # The standard project build supplies Mathlib and PEqualNP.Defs.
    subprocess.run(['lake','build','+PEqualNP.Defs'],cwd=lake_dir,check=True)
    lake_path = subprocess.check_output(['lake','env','printenv','LEAN_PATH'],
                                        cwd=lake_dir,text=True).strip()
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join([str(dest),lake_path])
    for unit in ['EncodedBank', 'SearchCore', 'VerifiedCore', *PROOFS]:
        print(f'Checking {unit}',flush=True)
        subprocess.run([lean,'-j1','-R','.','-o',unit+'.olean',unit+'.lean'],
                       cwd=dest,env=env,check=True)
    audit = dest/'Axioms.lean'
    audit.write_text('import FirstCert2\nimport FirstCert3\n'
                     '#print axioms PEqualNP.Research2836.First.extractedBank\n'
                     '#print axioms PEqualNP.Research2836.First.excludes_four\n'
                     '#print axioms PEqualNP.Research2836.FirstMemo3.root\n'
                     '#print axioms PEqualNP.Research2836.FirstMemo2.root\n')
    subprocess.run([lean,'-j1',audit.name],cwd=dest,env=env,check=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, help='project checkout containing lean/')
    parser.add_argument('--sources-only', action='store_true', help='check public source hashes and assembly')
    parser.add_argument('--download', action='store_true', help='obtain pinned sources directly from GitHub')
    args = parser.parse_args()
    if args.project:
        project = args.project.resolve()
    else:
        project = Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],
                                                cwd=HERE,text=True).strip())
    if not (project/'lean'/'lean-toolchain').is_file():
        parser.error('The project path must contain lean/lean-toolchain.')
    with tempfile.TemporaryDirectory(prefix='pequalnp-2836-') as scratch:
        dest = Path(scratch)
        prepare(project,dest,args.download)
        print('Pinned shared sources match the previously checked modules.',flush=True)
        if not args.sources_only:
            verify(project,dest)

if __name__ == '__main__':
    main()
