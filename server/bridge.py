"""A backend for proof games on the Lean REPL: Lean gets a context and a statement, and plays moves
(tactics) on proof states. The rules of a game (which tactics and theorems are allowed, hints) are
the frontend's business.

Copied from nng-verso (repl/bridge.py, ee6210b) and grown for a public server: a pool of REPL
processes, each in a sandbox, with a time limit per request and a limit on memory.

    cd ~/lean/journal && BASE="import Journal.Notes.DiscreteMeasure.Thinning" \
      REPL=~/lean/repl/.lake/build/bin/repl python3 -I bridge.py [port]      (default port 8091)

POST /start {"context": "open ProbGame", "statement": "example (p : I) : … = …"}
                                                         → {"session", "state": {"id", "goals", "solved"}}
POST /step  {"session", "state": 0, "tactic": "rw [h]"}  → {"state": …} or {"error": {"kind", "message"}}
POST /simp  {"context", "open": "DiscreteMeasure", "vars": "(p : unitInterval)", "rules": "coin_not', …", "expr": "(coin p).map not"}
                                                         → {"result": "coin (σ p)"}: the normal form of `expr`
                                                           by `#simp only [rules]`
POST /check {"session", "proof": "rw [h]\nrfl"}         → the proof state as lean4game's Game.getProofState
                                                           gives it (steps, diagnostics, completed)

Settings (environment):
  BASE       what each REPL loads first (default `import Game`)
  REPL       the REPL binary
  POOL       the number of REPL processes (default 1); a session stays with its process
  TIMEOUT    seconds Lean may take for one request (default 30); then the process is restarted
  MEMORY_GB  a process above this is killed and restarted (default 6); above half of it, it is
             restarted when it is idle, since a REPL keeps every state it has made
  SANDBOX=1  each REPL runs in bubblewrap: no network, the file system read-only and only the
             toolchain, the project and the REPL visible, so that Lean code from visitors (`#eval`
             with IO) can neither reach out nor read the home directory
  ALLOWED    a file with a SHA-256 of an accepted context per line (`sha256sum Lean/*.lean`);
             without it, any context

A session whose process was restarted is started again by the next /check, which plays the whole
proof anyway; /step on it answers that the session is gone.
"""
import contextlib, hashlib, json, os, queue, re, signal, subprocess, sys, threading, time, uuid
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

REPL = os.path.expanduser(os.environ.get('REPL', '~/lean/repl/.lake/build/bin/repl'))
BASE = os.environ.get('BASE', 'import Game')
POOL = int(os.environ.get('POOL', '1'))
TIMEOUT = float(os.environ.get('TIMEOUT', '30'))
MEMORY = float(os.environ.get('MEMORY_GB', '6')) * 2**30
SANDBOX = os.environ.get('SANDBOX') == '1'
# the contexts this server accepts (SHA-256 of their text, one per line); without the file, any
ALLOWED = ({l.split()[0] for l in Path(os.environ['ALLOWED']).read_text().splitlines() if l.strip() and not l.startswith('#')}
           if os.environ.get('ALLOWED') else None)
QUEUE = 8          # requests waiting for one process; beyond that the server is busy
BODY = 64 * 1024   # the largest request
IDLE = 3 * 3600    # a session not used for this long is forgotten


def command():
    """How a REPL is started: with the environment of `lake env` in the project (the current
    directory), in bubblewrap if SANDBOX."""
    env = dict(line.split('=', 1) for line in
               subprocess.run(['lake', 'env', 'env'], capture_output=True, text=True, check=True).stdout.splitlines() if '=' in line)
    keep = {k: v for k, v in env.items() if k.startswith(('LEAN', 'LAKE', 'ELAN')) or k in ('PATH', 'LD_LIBRARY_PATH')}
    if not SANDBOX:
        return [REPL], {**os.environ, **keep}
    sysroot, project, repl = env['LEAN_SYSROOT'], os.getcwd(), os.path.dirname(os.path.realpath(REPL))
    # (not --die-with-parent: it ties the sandbox to the thread that started it, and a request's
    # thread ends; the server kills its processes when it ends, see `stop`)
    args = ['bwrap', '--unshare-all', '--clearenv',
            '--ro-bind', '/usr', '/usr', '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
            '--symlink', 'usr/bin', '/bin', '--proc', '/proc', '--dev', '/dev', '--size', str(64 * 2**20), '--tmpfs', '/tmp',
            '--ro-bind', sysroot, sysroot, '--ro-bind', project, project, '--ro-bind', repl, repl, '--chdir', project,
            '--setenv', 'HOME', '/tmp']
    for k, v in keep.items():
        args += ['--setenv', k, v]
    return args + [os.path.realpath(REPL)], None


def errors_of(r):
    return [m['data'] for m in r.get('messages', []) if m.get('severity') == 'error']


class Repl:
    """One REPL process; one request at a time. It is restarted when it takes too long, ends, or
    grows too large; `generation` counts the starts, so that a session sees that its states are gone."""

    def __init__(self, n):
        self.n, self.generation, self.waiting = n, 0, 0
        self.lock = threading.RLock()
        self.p = None
        with self.lock:
            self.start()

    def start(self):
        if self.p:
            with contextlib.suppress(ProcessLookupError):
                os.killpg(self.p.pid, signal.SIGKILL)
            self.p.wait()
        cmd, env = COMMAND
        self.p = subprocess.Popen(cmd, env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.DEVNULL, text=True, bufsize=1, start_new_session=True)
        self.out = queue.Queue()
        threading.Thread(target=lambda p, q: ([q.put(l) for l in p.stdout], q.put(None)), args=(self.p, self.out), daemon=True).start()
        self.generation += 1
        self.contexts = {}
        t0 = time.time()
        self.base = self.ask({'cmd': BASE}, 900)['env']
        print(f"{time.strftime('%H:%M:%S')} REPL {self.n} started (generation {self.generation}, {time.time() - t0:.0f} s)", flush=True)

    @contextlib.contextmanager
    def use(self):
        """The process for one request: waits for it, and restarts it afterwards if it has grown."""
        self.waiting += 1
        try:
            with self.lock:
                yield self
                if self.rss() > MEMORY / 2:
                    print(f"{time.strftime('%H:%M:%S')} REPL {self.n} at {self.rss() / 2**30:.1f} GB: restart", flush=True)
                    self.start()
        finally:
            self.waiting -= 1

    def rss(self):
        """The memory of the process and its children (its process group): their own memory
        (RssAnon), not the .olean files they map, which all processes share."""
        total = 0
        for stat in Path('/proc').glob('[0-9]*/stat'):
            with contextlib.suppress(OSError, IndexError, ValueError, TypeError):
                if int(stat.read_text().rsplit(')', 1)[1].split()[2]) == self.p.pid:  # the process group
                    status = (stat.parent / 'status').read_text()
                    total += int(re.search(r'RssAnon:\s*(\d+)', status)[1]) * 1024
        return total

    def context(self, code):
        """The environment of a context (Lean code after the base), elaborated once per process."""
        if ALLOWED is not None and hashlib.sha256(code.encode()).hexdigest() not in ALLOWED:
            raise PermissionError('this server does not accept this context')
        if code not in self.contexts:
            r = self.ask({'cmd': code, 'env': self.base}) if code.strip() else {'env': self.base}
            if errors_of(r):
                raise ValueError('the context has errors: ' + '; '.join(errors_of(r)))
            self.contexts[code] = r['env']
        return self.contexts[code]

    def ask(self, obj, timeout=None):
        with self.lock:
            if self.p.poll() is not None:  # killed while idle (by `watch`)
                self.start()
                raise TimeoutError('Lean was restarted, please try again')
            self.p.stdin.write(json.dumps(obj) + '\n\n')
            self.p.stdin.flush()
            deadline, lines = time.time() + (timeout or TIMEOUT), []
            while True:
                try:
                    line = self.out.get(timeout=max(0, deadline - time.time()))
                except queue.Empty:
                    line = 'timeout'
                if line in (None, 'timeout'):
                    print(f"{time.strftime('%H:%M:%S')} REPL {self.n}: {'took too long' if line else 'ended'}, restart", flush=True)
                    if timeout:  # the base itself does not load: give up
                        raise RuntimeError('the REPL does not start')
                    self.start()
                    raise TimeoutError('Lean took too long (more than %d s)' % TIMEOUT if line else 'Lean ended unexpectedly')
                if line.strip() == '' and lines:
                    return json.loads(''.join(lines))
                if line.strip():
                    lines.append(line)


def watch():
    """Kills a process that grows beyond MEMORY while it works; its request then restarts it."""
    while True:
        time.sleep(2)
        for w in workers:
            if w.p and w.rss() > MEMORY:
                print(f"{time.strftime('%H:%M:%S')} REPL {w.n} above {MEMORY / 2**30:.0f} GB: killed", flush=True)
                with contextlib.suppress(ProcessLookupError):
                    os.killpg(w.p.pid, signal.SIGKILL)
        for sid, s in list(sessions.items()):
            if time.time() - s.used > IDLE:
                sessions.pop(sid, None)


def stop(*_):
    """Ends the server and its processes."""
    for w in workers:
        with contextlib.suppress(ProcessLookupError):
            os.killpg(w.p.pid, signal.SIGKILL)
    os._exit(0)


def worker():
    """The process with the fewest waiting requests."""
    w = min(workers, key=lambda w: w.waiting)
    if w.waiting >= QUEUE:
        raise OverflowError('Lean is busy, please try again in a moment')
    return w


class Session:
    def __init__(self, context, statement):
        self.context, self.statement = context, statement
        self.worker, self.used = worker(), time.time()
        with self.worker.use():
            self.begin()

    def begin(self):
        """The statement with `sorry` as its proof: the start state (on the session's process)."""
        w = self.worker
        r = w.ask({'cmd': self.statement + ' := by\n  sorry', 'env': w.context(self.context)})
        if errors_of(r) or not r.get('sorries'):
            raise ValueError('the statement has errors: ' + '; '.join(errors_of(r)))
        s = r['sorries'][0]
        self.start = {'id': s['proofState'], 'goals': [s['goal']], 'solved': False}
        self.generation = w.generation
        self.cache = {}  # (state, tactic) → the answer, so that a proof checked again costs nothing

    def step(self, state, tactic):
        key = (state, tactic)
        if key not in self.cache:
            r = self.worker.ask({'tactic': tactic, 'proofState': state})
            if 'message' in r and 'proofState' not in r:
                self.cache[key] = {'error': {'kind': 'lean', 'message': r['message'].removeprefix('Lean error:\n')}}
            elif errors_of(r):
                self.cache[key] = {'error': {'kind': 'lean', 'message': '\n'.join(errors_of(r))}}
            else:
                self.cache[key] = {'state': {'id': r['proofState'], 'goals': r.get('goals', []),
                                             'solved': r.get('proofStatus') == 'Completed'}}
        return self.cache[key]

    def check(self, proof):
        """The whole proof, line by line, as lean4game's Game.getProofState answers."""
        if self.generation != self.worker.generation:
            self.begin()
        goals = lambda gs: [{'goal': {'text': g}, 'hints': []} for g in gs]
        steps = [{'line': 0, 'goals': goals(self.start['goals']), 'diags': []}]
        state, solved = self.start, False
        for i, line in enumerate(proof.split('\n')):
            tactic = re.sub(r'^\s*·\s*', '', line).strip()
            if not tactic or tactic.startswith('--'):
                continue
            r = self.step(state['id'], tactic)
            if 'error' in r:
                steps.append({'line': i + 1, 'goals': goals(state['goals']), 'diags': [{
                    'severity': 1, 'range': {'start': {'line': i, 'character': 0}, 'end': {'line': i, 'character': len(line)}},
                    'message': {'text': r['error']['message']}}]})
                return {'steps': steps, 'diagnostics': [], 'completed': False}
            state = r['state']
            steps.append({'line': i + 1, 'goals': goals(state['goals']), 'diags': []})
            solved = state['solved']
        return {'steps': steps, 'diagnostics': [], 'completed': solved}


COMMAND = None
workers = []
sessions = {}
forms = {}  # (context, vars, rules, expr, open) → the answer


def normal_form(req):
    """The normal form of an expression by `#simp only [rules]`, in a context (elaborated once)."""
    key = (req.get('context', ''), req.get('vars', ''), req.get('rules', ''), req['expr'], req.get('open', ''))
    if key not in forms:
        with worker().use() as w:
            cmd = (f"open {key[4]} in\n" if key[4] else '') + (f"variable {key[1]} in\n" if key[1] else '') + f"#simp only [{key[2]}] => {key[3]}"
            r = w.ask({'cmd': cmd, 'env': w.context(key[0])})
        infos = [m['data'] for m in r.get('messages', []) if m.get('severity') == 'info']
        if len(forms) > 100_000:
            forms.clear()
        forms[key] = {'error': {'kind': 'lean', 'message': '\n'.join(errors_of(r))}} if errors_of(r) or not infos else {'result': infos[-1].strip()}
    return forms[key]


class Handler(BaseHTTPRequestHandler):
    def cors(self):
        self.send_header('Access-Control-Allow-Origin', '*')
        self.send_header('Access-Control-Allow-Headers', 'Content-Type')
        self.send_header('Access-Control-Allow-Methods', 'POST, OPTIONS')
        # (a page on the web may then ask a bridge on 127.0.0.1, e.g. through an SSH tunnel: Chrome's
        # Private Network Access)
        self.send_header('Access-Control-Allow-Private-Network', 'true')

    def do_OPTIONS(self):
        self.send_response(204)
        self.cors()
        self.end_headers()

    def answer(self, obj, code=200):
        # one line per request: when, who, what, the outcome, how long
        bad = [(st['line'], d['message']['text']) for st in obj.get('steps', []) for d in st['diags'] if d.get('severity') == 1]
        outcome = (obj['error'].get('message', '') if 'error' in obj
                   else f"= {obj['result']}" if 'result' in obj
                   else f"error in line {bad[0][0]}: {bad[0][1]}" if bad
                   else 'solved' if obj.get('completed') or obj.get('state', {}).get('solved') else 'ok')
        outcome = ' '.join(outcome.split())[:90]
        who = self.headers.get('X-Real-IP') or self.client_address[0]
        print(f"{time.strftime('%H:%M:%S')} {who} {getattr(self, 'what', self.path)} → {outcome} ({(time.time() - getattr(self, 't0', time.time())) * 1000:.0f} ms)", flush=True)
        body = json.dumps(obj).encode()
        self.send_response(code)
        self.cors()
        self.send_header('Content-Type', 'application/json')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_POST(self):
        self.t0, self.what = time.time(), self.path
        try:
            n = int(self.headers.get('Content-Length', 0))
            if n > BODY:
                return self.answer({'error': {'kind': 'size', 'message': 'the request is too large'}}, 413)
            req = json.loads(self.rfile.read(n) or b'{}')
            self.what = f"{self.path} {req.get('statement', '')[:50] or req.get('expr', '')[:70] or (req.get('tactic') or (req.get('proof') or '').strip().replace(chr(10), '; '))[:60]}"

            if self.path == '/start':
                sid = uuid.uuid4().hex[:12]
                sessions[sid] = Session(req.get('context', ''), req['statement'])
                return self.answer({'session': sid, 'state': sessions[sid].start})
            if self.path == '/simp':
                return self.answer(normal_form(req))
            s = sessions.get(req.get('session'))
            if not s:
                return self.answer({'error': {'kind': 'session', 'message': 'unknown session'}}, 404)
            s.used = time.time()
            with s.worker.use():
                if self.path == '/step':
                    if s.generation != s.worker.generation:
                        return self.answer({'error': {'kind': 'session', 'message': 'the session is gone (Lean was restarted)'}}, 404)
                    return self.answer(s.step(int(req['state']), req['tactic']))
                if self.path == '/check':
                    return self.answer(s.check(req.get('proof', '')))
            self.answer({'error': {'kind': 'path', 'message': self.path}}, 404)
        except PermissionError as e:
            self.answer({'error': {'kind': 'context', 'message': str(e)}}, 403)
        except OverflowError as e:
            self.answer({'error': {'kind': 'busy', 'message': str(e)}}, 503)
        except TimeoutError as e:
            self.answer({'error': {'kind': 'timeout', 'message': str(e)}}, 200)
        except Exception as e:  # a request that cannot be answered must not end the server
            self.answer({'error': {'kind': 'server', 'message': f'{type(e).__name__}: {e}'}}, 500)

    def log_message(self, *args):
        pass


if __name__ == '__main__':
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8091
    COMMAND = command()
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    starting = [threading.Thread(target=lambda n=n: workers.append(Repl(n))) for n in range(POOL)]
    for t in starting:
        t.start()
    for t in starting:
        t.join()
    workers.sort(key=lambda w: w.n)
    threading.Thread(target=watch, daemon=True).start()
    print(f"{len(workers)} REPL{'s' if len(workers) > 1 else ''}{' in bubblewrap' if SANDBOX else ''}, at http://127.0.0.1:{port}/", flush=True)
    ThreadingHTTPServer(('127.0.0.1', port), Handler).serve_forever()
