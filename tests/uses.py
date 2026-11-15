"""Writes `(uses := "…")` into every level that has a `:::solution`: the theorems (rules and lemmas of
the inventory in game.js) that its solution uses. The game then shows only these theorems in the
level (all the tactics earned stay). A level whose `uses` was set by hand keeps it: mark it with
`(uses := "!…")`.
    python3 tests/uses.py            (all worlds of ProbGame/Worlds)"""
import re, glob, pathlib
root = pathlib.Path(__file__).resolve().parent.parent
js = (root / 'ProbGame/game.js').read_text()
theorems = set(re.findall(r"\{ name: '([^']+)', kind: '(?:rule|lemma)'", js)) | set(re.findall(r'\{ name: "([^"]+)", kind: \'(?:rule|lemma)\'', js))
# The natural partners of a theorem: shown with it (when earned), so that the inventory may also lead
# astray a little, without being convoluted.
PAIRS = [('coin_true', 'coin_false'), ('Bool.cond_true', 'Bool.cond_false'), ('Bool.not_true', 'Bool.not_false'),
         ('bind_true', 'bind_false'), ('zero_add', 'add_zero'), ('mul_one', 'one_mul'), ('mul_zero', 'zero_add'),
         ('pow_zero', 'pow_succ'), ('shift_succ', 'shift_zero'), ('pure_bind', 'bind_pure'),
         ('map_bind', 'bind_map_left'), ('binom_zero', 'binom_succ'), ('geom_zero', 'geom_succ'),
         ('hyper_zero', 'hyper_succ'), ('hyper_black', 'hyper_white'), ('coin_zero', 'coin_one'),
         ('frac_zero', 'frac_white'), ('seq_zero', 'seq_succ'), ('Bool.and_not_self', 'Bool.or_not_self'),
         ('coin_unused', 'prob_unused'), ('binom_succ_zero', 'binom_succ_succ'), ('binom_all_false', 'binom_diag'),
         ('add_comm', 'add_assoc'), ('mass_total', 'coin_total'), ('pure_self', 'pure_zero_succ'),
         ('Nat.choose_self', 'Nat.choose_zero_right'), ('Nat.cast_add', 'Nat.cast_one'), ('add_assoc', 'add_right_comm')]
partners = {}
for a, b in PAIRS: partners.setdefault(a, []).append(b); partners.setdefault(b, []).append(a)
for f in sorted(glob.glob(str(root / 'ProbGame/Worlds/*.lean'))):
    lines = open(f).read().split('\n'); changed = 0
    i = 0
    while i < len(lines):
        if re.match(r'^::::(circuit|leanonly) ', lines[i]):
            end = next(j for j in range(i + 1, len(lines)) if lines[j] == '::::')
            body = lines[i + 1:end]
            if ':::solution' in body and '(uses := "!' not in lines[i]:
                k = body.index(':::solution') + 2; sol = []
                while body[k] != '```': sol.append(body[k]); k += 1
                used = []
                for t in re.findall(r"[A-Za-z_][\w.']*", '\n'.join(sol)):
                    if t in theorems and t not in used: used.append(t)
                for t in list(used):
                    for u in partners.get(t, []):
                        if u in theorems and u not in used: used.append(u)
                new = re.sub(r' \(uses := "[^"]*"\)', '', lines[i]) + (f' (uses := "{", ".join(used)}")' if used else ' (uses := "-")')
                if new != lines[i]: lines[i] = new; changed += 1
            i = end
        i += 1
    if changed: open(f, 'w').write('\n'.join(lines)); print(pathlib.Path(f).name, changed)
