"""Plays the solutions of Lean/Solutions0.lean and Lean/Solutions.lean through a bridge, line by line, as the game does.

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
# world 0 has a context of its own
for solutions, rules in [('Solutions0.lean', 'World0.lean'), ('Solutions.lean', 'Rules.lean')]:
    context = (here / 'Lean' / rules).read_text()
    for block in (here / 'Lean' / solutions).read_text().split('\nexample ')[1:]:
        head, body = block.split(' := by\n', 1)
        proof = '\n'.join(l[2:] for l in body.split('\n') if l.startswith('  '))
        s = post('/start', {'context': context, 'statement': 'example ' + head})
        c = post('/check', {'session': s['session'], 'proof': proof}) if 'session' in s else s
        ok = c.get('completed')
        failures += not ok
        print('ok  ' if ok else 'FAIL', ' '.join(head.split())[:90])
print(f'{failures} failures')
sys.exit(1 if failures else 0)
