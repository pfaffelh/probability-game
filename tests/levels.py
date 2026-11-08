"""The levels of the game, read from their sources (`ProbGame/Worlds/*.lean`), for the tests: for
each world (its module, as in `data-world` of its levels) its levels in order, each with its kind,
the edition it is for (`main`, `show`, or none: both), the moves that solve its board (`play`), its
statement (`proof`), its solution (`:::solution`, line by line) and the file of its rules.

    python3 -I tests/levels.py          (JSON on stdout)
"""
import json, re, sys
from pathlib import Path

here = Path(__file__).resolve().parent.parent
HEAD = re.compile(r'^::::(level|build|boolean|walk) ')
# the rules the proofs of a kind of level are checked in, when the level names none
CONTEXT = {'level': ('proofContext', 'Lean/Rules.lean'), 'build': ('proofContext', 'Lean/Rules.lean'),
           'boolean': ('context', 'Lean/WorldBool.lean'), 'walk': ('context', 'Lean/WorldWalk.lean')}


def attr(line, k):
    m = re.search(r'\(' + k + r' := "((?:[^"\\]|\\.)*)"\)', line)
    return m.group(1).replace('\\"', '"') if m else None


def levels_of(path):
    lines, out, edition = path.read_text().split('\n'), [], None
    i = 0
    while i < len(lines):
        l = lines[i]
        if l.startswith(':::::only'):
            edition = attr(l, 'edition')
        elif l == ':::::':
            edition = None
        elif HEAD.match(l):
            kind = HEAD.match(l).group(1)
            end = next(j for j in range(i + 1, len(lines)) if lines[j] == '::::')
            body = lines[i + 1:end]
            solution = []
            if ':::solution' in body:
                k = body.index(':::solution') + 2          # after the opening ```
                solution = body[k:body.index('```', k)]
            key, default = CONTEXT[kind]
            out.append({'kind': kind, 'edition': edition, 'play': attr(l, 'play') or '',
                        'proof': attr(l, 'proof'), 'lemma': attr(l, 'lemma'), 'solution': solution,
                        'context': attr(l, key) or default})
            i = end
        i += 1
    return out


def worlds():
    return {'ProbGame.Worlds.' + p.stem: levels_of(p) for p in sorted((here / 'ProbGame' / 'Worlds').glob('*.lean'))}


if __name__ == '__main__':
    json.dump(worlds(), sys.stdout, ensure_ascii=False, indent=1)
