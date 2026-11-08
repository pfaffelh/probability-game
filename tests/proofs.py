"""Plays the solution of every level through a bridge, as the game does: the statement of the level
in the context of its rules, then its `:::solution`, read from the sources (tests/levels.py).

    python3 -I tests/proofs.py [http://127.0.0.1:8091]

The bridge runs in the journal with BASE="import Journal.Notes.DiscreteMeasure.Thinning" (see README).
"""
import json, sys, urllib.request
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from levels import worlds, here

bridge = sys.argv[1] if len(sys.argv) > 1 else 'http://127.0.0.1:8091'


def post(path, obj):
    req = urllib.request.Request(bridge + path, json.dumps(obj).encode(), {'Content-Type': 'application/json'})
    return json.loads(urllib.request.urlopen(req).read())


failures = 0
for world, levels in worlds().items():
    print(f'-- {world}')
    for l in levels:
        if not l['proof']:
            continue
        if not l['solution']:
            failures += 1; print('FAIL no :::solution for', l['proof'][:80]); continue
        context = (here / l['context']).read_text()
        s = post('/start', {'context': context, 'statement': 'example ' + l['proof']})
        c = post('/check', {'session': s['session'], 'proof': '\n'.join(l['solution'])}) if 'session' in s else s
        ok = c.get('completed')
        failures += not ok
        print('ok  ' if ok else 'FAIL', ' '.join(l['proof'].split())[:90])
print(f'{failures} failures')
sys.exit(1 if failures else 0)
