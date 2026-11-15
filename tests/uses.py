"""Writes `(uses := "…")` into every level that has a `:::solution`: the theorems (rules and lemmas of
the inventory in game.js) that its solution uses. The game then shows only these theorems in the
level (all the tactics earned stay). A level whose `uses` was set by hand keeps it: mark it with
`(uses := "!…")`.
    python3 tests/uses.py            (all worlds of ProbGame/Worlds)"""
import re, glob, pathlib
root = pathlib.Path(__file__).resolve().parent.parent
js = (root / 'ProbGame/game.js').read_text()
theorems = set(re.findall(r"\{ name: '([^']+)', kind: '(?:rule|lemma)'", js)) | set(re.findall(r'\{ name: "([^"]+)", kind: \'(?:rule|lemma)\'', js))
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
                new = re.sub(r' \(uses := "[^"]*"\)', '', lines[i]) + (f' (uses := "{", ".join(used)}")' if used else ' (uses := "-")')
                if new != lines[i]: lines[i] = new; changed += 1
            i = end
        i += 1
    if changed: open(f, 'w').write('\n'.join(lines)); print(pathlib.Path(f).name, changed)
