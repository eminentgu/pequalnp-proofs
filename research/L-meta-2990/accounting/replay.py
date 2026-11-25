"""Kernel-check the sparse incidence counting proof in a temporary directory."""
import argparse
import shutil
import subprocess
import tempfile
from pathlib import Path


HERE = Path(__file__).resolve().parent
BASE = 'a46f34ec89b6d6d8c53184b7b8eda4a2a8acf7ae'


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('repo', type=Path, help='pequalnp-proofs checkout with its Lean toolchain built')
    cli.add_argument('--single', type=Path, help='also write an import-Defs standalone research proof')
    args = cli.parse_args()
    repo = args.repo.resolve()
    with tempfile.TemporaryDirectory() as tmp:
        scratch = Path(tmp)
        for task in ('2466', '2673'):
            name = f'L_meta_{task}.lean'
            text = subprocess.check_output(['git', '-C', str(repo), 'show',
                                        f'{BASE}:lean/PEqualNP/Outside/{name}'])
            (scratch / name).write_bytes(text)
        subprocess.run(['python3', str(HERE / 'strengthen.py'), str(scratch), str(scratch/'SharpTwice.lean')], check=True)
        subprocess.run(['python3', str(HERE / 'assemble.py'), str(scratch/'L_meta_2673.lean'), str(scratch/'FinalAccounting.lean')], check=True)
        shutil.copy(HERE / 'Density.lean', scratch / 'Density.lean')
        if args.single:
            lines = ['import Mathlib', 'import PEqualNP.Defs', '']
            for unit in ('SharpTwice', 'FinalAccounting', 'Density'):
                lines.extend(x for x in (scratch / f'{unit}.lean').read_text().splitlines()
                             if not x.startswith(('import ', '#print ')))
            lines += ['', '#print axioms Incidence2990.lossBound', '#print axioms Incidence2990.hardDensity']
            args.single.write_text('\n'.join(lines)+'\n')
        subprocess.run(['lake','env','sh','-ec',
                        'cd "$1"; export LEAN_NUM_THREADS=1 LEAN_PATH="$1:$LEAN_PATH"; '
                        'for unit in SharpTwice FinalAccounting Density; do lean -j1 -o "$unit.olean" "$unit.lean"; done',
                        'replay',str(scratch)], cwd=repo/'lean', check=True)


if __name__ == '__main__':
    main()
