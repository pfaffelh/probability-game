"""Checks other solutions of levels as the game would: the statement of the level (gaps filled as
meant) in the context of its rules, the proof with the game's simp (simp only with the simp rules of
the level's inventory), and which tactics and theorems of the proof are not in the level's inventory.

    python3 -I tests/alt.py batch.json [bridge]     batch.json: [["Masses", 5, "rw [← mass_total μ, h, zero_add]"], …]

World names as the modules (Circuits, Masses, OneCoin, Maps, TwoCoins, DoLaws, Counting, Bind,
RealNumbers, Sequences, Binomial, Geometric, Thinning, Hypergeometric); levels counted from 1 as on the
page. Needs the built site (_out/html-multi) and a bridge (see README). Prints one line per proof:
OK or FAIL (with Lean's first error), and `missing:` the names not in the inventory there."""
import html, json, re, sys, urllib.request
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from levels import worlds, here

SLUG = {'Circuits': 'Circuits', 'Masses': 'DiscreteMeasure', 'OneCoin': 'One-Coin', 'Maps': 'Maps', 'TwoCoins': 'Two-Coins',
        'DoLaws': 'Laws-of--do', 'Counting': 'Counting', 'Bind': 'Multi-Stage-Experiments', 'RealNumbers': 'Balance',
        'Sequences': 'Sequences', 'Binomial': 'Binomial', 'Geometric': 'Geometric', 'Thinning': 'Thinning', 'Hypergeometric': 'Hypergeometric'}
js = (here / 'ProbGame/game.js').read_text()
names = re.findall(r"""\{ name: (?:'([^']+)'|"([^"]+)"), kind: '(tactic|rule|lemma)'""", js)
KIND = {a or b: k for a, b, k in names}
def strlist(name):
    m = re.search(r'const ' + name + r' = \[(.*?)\]', js, re.S)
    return re.findall(r"'([^']+)'", m.group(1))
SIMP_ALWAYS, SIMP_ITEMS = strlist('SIMP_ALWAYS'), strlist('SIMP_ITEMS')
bridge = sys.argv[2] if len(sys.argv) > 2 else 'http://127.0.0.1:8091'
W = worlds()


def post(path, obj):
    req = urllib.request.Request(bridge + path, json.dumps(obj).encode(), {'Content-Type': 'application/json'})
    return json.loads(urllib.request.urlopen(req, timeout=120).read())


def page_levels(world):
    """per level of the page: (inventory, new) as sets, or None for a level without a proof"""
    s = (here / '_out/html-multi' / SLUG[world] / 'index.html').read_text()
    out = []
    for part in re.split(r'<div class="pg-level[ "]', s)[1:]:
        inv = re.search(r'data-inventory="([^"]*)"', part.split('<div class="pg-level')[0])
        new = re.search(r'data-new="([^"]*)"', part.split('<div class="pg-level')[0])
        uses = re.search(r'data-uses="([^"]*)"', part.split('<div class="pg-level')[0])
        without = {x.strip()[1:] for x in html.unescape(uses.group(1) if uses else '').split(',') if x.strip().startswith('-') and len(x.strip()) > 1}
        out.append((set(json.loads(html.unescape(inv.group(1)))) - without, set(json.loads(html.unescape(new.group(1))))) if inv else None)
    return out


def check(world, n, proof):
    levels = [l for l in W['ProbGame.Worlds.' + world] if not l['edition'] or l['edition'] == 'main']
    l = levels[n - 1]
    pl = page_levels(world)
    inv, new = pl[n - 1] if n - 1 < len(pl) and pl[n - 1] else (set(), set())
    rules = [r for r in SIMP_ALWAYS + [x for x in SIMP_ITEMS if x in inv] if r not in new]
    lean = '\n'.join('<;>'.join(re.sub(r'^(\s*)simp(?:\s*\[(.*)\])?\s*$', lambda m: f"{m.group(1)}simp only [{', '.join(rules + ([m.group(2)] if m.group(2) else []))}] ", p)
                                for p in line.split('<;>')) for line in proof.split('\n'))
    # what the proof uses that the inventory there does not have
    toks = set(re.findall(r"[A-Za-z_][\w.']*", proof)) | ({'<;>'} if '<;>' in proof else set())
    missing = sorted(t for t in toks if t in KIND and t not in inv)
    tactics = {re.match(r"\s*(?:·\s*)?([\w']+(?: only)?)", p).group(1) for line in proof.split('\n') for p in line.split('<;>') if re.match(r"\s*(?:·\s*)?[\w']", p)}
    unknown = sorted(t for t in tactics if t not in KIND and t not in ('at',))
    # (as the game: a name with . or _ that is neither in the inventory nor a name of the statement or
    # of the proof (induction' … with n ih) is refused)
    local = set(re.findall(r"[A-Za-z_][\w']*", l['proof'] or '')) | {x for m in re.findall(r"with ([\w' ]+)", proof) for x in m.split()}
    unknown += sorted(t for t in set(re.findall(r"(?<![\w.'])[A-Za-z_][\w.']*", proof))
                      if re.search(r'[._]', t) and t != '_' and t not in KIND and t not in local and t.split('.')[0] not in local)
    context = (here / l['context']).read_text()
    s = post('/start', {'context': context, 'statement': 'example ' + l['proof']})
    if 'session' not in s:
        return False, str(s.get('error', s))[:200], missing, unknown
    c = post('/check', {'session': s['session'], 'proof': lean})
    bad = [g['message']['text'] for x in c.get('steps', []) for g in x['diags'] if g['severity'] == 1]
    ok = not bad and bool(c.get('completed'))
    return ok, '' if ok else (bad[0] if bad else 'goals remain'), missing, unknown


if __name__ == '__main__':
    for world, n, proof in json.load(open(sys.argv[1])):
        ok, err, missing, unknown = check(world, n, proof)
        print(f"{'OK  ' if ok else 'FAIL'} {world} {n}: {proof.replace(chr(10), ' / ')}"
              + (f"  | missing: {', '.join(missing)}" if missing else '') + (f"  | not in the game: {', '.join(unknown)}" if unknown else '')
              + ('' if ok else '  | ' + ' '.join(err.split())[:160]))
