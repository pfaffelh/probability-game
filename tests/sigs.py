#!/usr/bin/env python3
"""The full Lean statements of the inventory's theorems, for the inventory's popup (hover, long press).

Reads the names from ProbGame/game.js (INVENTORY, kind rule or lemma), asks Lean `#check name` for each
in the rules' context (Lean/Rules.lean, base `import Journal.Notes.DiscreteMeasure.Thinning`), and
writes them into game.js between `// LEAN_SIGS begin` and `// LEAN_SIGS end`. A name Lean does not
know (a rule of another branch) is left out; its popup shows the short form `sig`.
Usage: python3 tests/sigs.py [journal]   (default ~/Code/lean/journal)
"""
import json, re, subprocess, sys, tempfile
from pathlib import Path

here = Path(__file__).resolve().parent.parent
journal = Path(sys.argv[1] if len(sys.argv) > 1 else Path.home() / 'Code/lean/journal')
js = (here / 'ProbGame/game.js').read_text()
names = list(dict.fromkeys(re.findall(r"\{ name: '([^']+)', kind: '(?:rule|lemma)'", js)))
rules = (here / 'Lean/Rules.lean').read_text()
head, sep, tail = rules.rpartition('end ProbGame')
lines = ['import Journal.Notes.DiscreteMeasure.Thinning'] + head.splitlines()
first = len(lines) + 1
lines += ['set_option pp.universes false', 'set_option pp.mvars false'] + [f'#check {n}' for n in names] + [sep + tail]
with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as f:
    f.write('\n'.join(lines))
out = subprocess.run(['lake', 'env', 'lean', '--json', f.name], cwd=journal, capture_output=True, text=True).stdout
sigs = {}
for l in out.splitlines():
    try: m = json.loads(l)
    except ValueError: continue
    i = m['pos']['line'] - first - 2
    if m['severity'] == 'information' and 0 <= i < len(names):
        # (one line: the lines of a do block with `;` between them, as the inventory writes them)
        ls = m['data'].split('\n')
        t = ls[0]
        for prev, l in zip(ls, ls[1:]):
            t += ('; ' if re.match(r'^(.*\bdo\s+)?let\s[^←]*←', prev.strip()) else ' ') + l.strip()
        t = re.sub(r'\s+', ' ', t).strip()
        t = re.sub(r'^ProbGame\.', '', re.sub(r'^(\S+?)\.\{[^}]*\}', r'\1', t))
        t = t.replace(': ↑I)', ': I)')  # (as the goals show it)
        sigs[names[i]] = 'theorem ' + names[i] + ' ' + t.split(' ', 1)[1]  # (named as the player writes it)
missing = [n for n in names if n not in sigs]
if missing: print('not known to Lean here:', ', '.join(missing), file=sys.stderr)
block = '// LEAN_SIGS begin (written by tests/sigs.py)\n  const LEAN_SIGS = ' + json.dumps(sigs, ensure_ascii=False, indent=0).replace('\n', '\n    ') + '\n  // LEAN_SIGS end'
js2, n = re.subn(r'// LEAN_SIGS begin.*?// LEAN_SIGS end', lambda _: block, js, flags=re.S)
if not n: sys.exit('no LEAN_SIGS markers in game.js')
(here / 'ProbGame/game.js').write_text(js2)
print(f'{len(sigs)} statements')
