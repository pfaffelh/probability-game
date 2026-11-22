"""Three meetings: every tactic should be introduced, practised in its world, and used again in a later
one. Counts, from the solutions of the levels (`:::solution`), in how many levels and worlds each
tactic occurs, and warns of a tactic in fewer than three levels or in one world only.
    python3 tests/tactics.py         (exit code 1 when a tactic is thin)"""
import json, re, subprocess, sys, pathlib
root = pathlib.Path(__file__).resolve().parent.parent
TACTICS = ['rfl', 'rw', 'cases', 'exact', 'apply', 'constructor', 'ext', 'revert', 'decide', 'simp_rw', 'simp only',
           'simp', 'congr', 'ring', "induction'", 'linear_combination', 'field_simp', 'intro', 'have', 'funext', 'exists']
pat = re.compile(r'^(' + '|'.join(re.escape(t) for t in sorted(TACTICS, key=len, reverse=True)) + r')(?=\s|\[|$)')
worlds = json.loads(subprocess.run([sys.executable, '-I', str(root / 'tests/levels.py')], capture_output=True, text=True, check=True).stdout)
# the worlds of the game, in its order (`{include 1 ProbGame.Worlds.X}` in ProbGame.lean)
order = re.findall(r'\{include 1 (ProbGame\.Worlds\.\w+)\}', (root / 'ProbGame.lean').read_text())
worlds = {w.split('.')[-1]: worlds[w] for w in order}
levels, lines = {}, {}
for world, ls in worlds.items():
    for n, l in enumerate(ls, 1):
        tactics = l.get('tactic', '').split(';') if l['kind'] == 'quiz' else [p for line in l.get('solution', []) for p in line.split('<;>')]
        for t in tactics:
            m = pat.match(t.strip())
            if m:
                levels.setdefault(m.group(1), {}).setdefault(world, set()).add(n)
                lines[m.group(1)] = lines.get(m.group(1), 0) + 1
thin = 0
for t in TACTICS:
    by = levels.get(t, {})
    if not by: continue
    count = sum(len(v) for v in by.values())
    bad = count < 3 or len(by) < 2
    thin += bad
    print(f"{'!' if bad else ' '} {t:19} {count:3} levels, {lines[t]:3} lines, {len(by):2} worlds: " + ', '.join(f'{w} {len(v)}' for w, v in by.items()))
sys.exit(1 if thin else 0)
