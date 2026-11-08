"""Plays the solutions of every world through a bridge, line by line, as the game does: for each
`tests/worlds/<World>.json` whose files are here, the proofs of `Lean/<solutions>` in the context
`Lean/<context>`.

    python3 -I tests/proofs.py [http://127.0.0.1:8091]

The bridge runs in the journal with BASE="import Journal.Notes.DiscreteMeasure.Thinning" (see README).
"""
import json, sys, urllib.request
from pathlib import Path

here = Path(__file__).resolve().parent.parent
bridge = sys.argv[1] if len(sys.argv) > 1 else 'http://127.0.0.1:8091'


def post(path, obj):
    req = urllib.request.Request(bridge + path, json.dumps(obj).encode(), {'Content-Type': 'application/json'})
    return json.loads(urllib.request.urlopen(req).read())


failures = 0
for f in sorted((here / 'tests' / 'worlds').glob('*.json')):
    w = json.loads(f.read_text())
    context = (here / 'Lean' / w['context']).read_text()
    print(f'-- {f.stem}: Lean/{w["solutions"]} in Lean/{w["context"]}')
    for block in (here / 'Lean' / w['solutions']).read_text().split('\nexample ')[1:]:
        head, body = block.split(' := by\n', 1)
        proof = '\n'.join(l[2:] for l in body.split('\n') if l.startswith('  '))
        s = post('/start', {'context': context, 'statement': 'example ' + head})
        c = post('/check', {'session': s['session'], 'proof': proof}) if 'session' in s else s
        ok = c.get('completed')
        failures += not ok
        print('ok  ' if ok else 'FAIL', ' '.join(head.split())[:90])
print(f'{failures} failures')
sys.exit(1 if failures else 0)
