"""Verify the uniform monotone case against the public L-meta-1922 source."""
import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
from urllib.request import urlopen

HERE = Path(__file__).resolve().parent
REV = 'f5b0e4e43b029c6b9fc316bbc8fdf6fcfa4c8a46'
NAME = 'lean/PEqualNP/Outside/L_meta_1922.lean'
SHA = '174776640ee9f28e3629f74697829312a96bba0264e76eefc4262267dfe16dc9'

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project',type=Path)
    args = parser.parse_args()
    project = args.project or Path(subprocess.check_output(
        ['git','rev-parse','--show-toplevel'],cwd=HERE,text=True).strip())
    project = project.resolve()
    lake = project/'lean'
    lean = subprocess.check_output(['elan','which','lean'],cwd=lake,text=True).strip()
    subprocess.run(['lake','build','+PEqualNP.Defs'],cwd=lake,check=True)
    path = subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=lake,text=True).strip()
    source = subprocess.run(['git','show',f'{REV}:{NAME}'],cwd=project,capture_output=True)
    if source.returncode == 0:
        data = source.stdout
    else:
        url = f'https://raw.githubusercontent.com/open-goat/pequalnp-proofs/{REV}/{NAME}'
        with urlopen(url,timeout=60) as response:
            data = response.read()
    if hashlib.sha256(data).hexdigest() != SHA:
        raise SystemExit('L-meta-1922 source hash mismatch.')
    with tempfile.TemporaryDirectory(prefix='monotone-2836-') as folder:
        dest = Path(folder)
        for shared in (lake/'.lake/build/lib/lean/PEqualNP').glob('Defs*'):
            (dest/'PEqualNP').mkdir(exist_ok=True)
            (dest/'PEqualNP'/shared.name).symlink_to(shared,target_is_directory=shared.is_dir())
        file = Path('PEqualNP/Outside/L_meta_1922.lean')
        (dest/file.parent).mkdir(parents=True,exist_ok=True)
        (dest/file).write_bytes(data)
        names = ['MonotoneTransport','MonotoneExact','CheckedMonotone']
        for name in names:
            (dest/(name+'.lean')).write_bytes((HERE/(name+'.lean')).read_bytes())
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(dest),path]), LEAN_NUM_THREADS='1')
        units = [Path(names[0]+'.lean'),Path(names[1]+'.lean'),file,Path(names[2]+'.lean')]
        for item in units:
            print('Checking',item,flush=True)
            subprocess.run([lean,'-j1','-R','.','-o',str(item.with_suffix('.olean')),str(item)],
                           cwd=dest,env=env,check=True)

if __name__ == '__main__':
    main()
