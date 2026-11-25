"""Emit independent kernel checks for each layer of the finite exclusion proof."""
from pathlib import Path
import json

work = Path(__file__).resolve().parent
layers = json.loads((work/'states94.json').read_text())['layers']
actions = json.loads((work/'actions94.json').read_text())['layers']

def key(words):
    return sum(w << (16*i) for i,w in enumerate(words)) + (1 << (16*len(words)))

def allowed(k,i):
    ids = sorted({a[-1] for a in actions[str(k)][i]})
    return [(j, key(layers[str(k-1)][j])) for j in ids]

def leanList(keys):
    return '[' + ','.join(hex(x) for x in keys) + ']'

def emit():
    case=work/'Case94'
    case.mkdir(exist_ok=True)
    for k in range(3,12):
        rows=layers[str(k)]
        shard=64
        count=(len(rows)+shard-1)//shard
        for block in range(count):
            start=block*shard
            imports={'Node94'}
            body=['','namespace Mono94.Case94','', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0','']
            for i in range(start,min(start+shard,len(rows))):
                children=allowed(k,i)
                for j,q in children:
                    imports.add(f'Case94.L{k-1}B{j//shard}')
                stat=hex(key(rows[i]))
                proof='nilDead'
                for j,_ in reversed(children):
                    proof=f'(consDead x{k-1}_{j} {proof})'
                body.append(f'theorem x{k}_{i} : Dead {k} {stat} := stepNode {k-1} {stat} {leanList(q for j,q in children)} (by decide +kernel) (by decide +kernel) {proof}')
            file=case/f'L{k}B{block}.lean'
            text = '\n'.join('import '+m for m in sorted(imports))+'\n'+'\n'.join(body+['','end Mono94.Case94',''])
            if not file.is_file() or file.read_text() != text:
                file.write_text(text)
    print(len(list(case.glob('*.lean'))),'shards',sum(p.stat().st_size for p in case.glob('*.lean')),'source bytes')

if __name__ == '__main__':
    emit()
