# The public server

The game runs on a Linux machine without root, behind a reverse proxy that does HTTPS and forwards
to port 8080. One nginx serves the site and passes `/lean/` to the bridge; the bridge keeps a pool
of Lean REPLs, each in bubblewrap.

| File | What |
|---|---|
| `bridge.py` | Lean for the game: `/start`, `/check`, `/step`, `/simp` (see its docstring) |
| `nginx.conf` | the site and `/lean/` on 8080, a limit on requests per visitor |
| `systemd/` | the two user services, `probgame-bridge` and `probgame-web` |
| `deploy.sh` | fetch, build, restart |

## What the machine needs (once, by its administrators)

* packages `bubblewrap`, `nginx`, `git`, `curl`, `python3` (no C compiler: `deploy.sh` compiles the
  little C there is with the clang of the Lean toolchain, and unpacks the C headers of glibc and
  Linux from Ubuntu's packages into `~/lean/sysroot`, without root);
* `loginctl enable-linger <user>`, so that the user services run without a login;
* user namespaces for `bwrap` (on Ubuntu 26.04 the `apparmor` package allows them with its
  profile `bwrap-userns-restrict`);
* no connections from the machine into the internal network.

## The first time

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
mkdir -p ~/lean && cd ~/lean
git clone -b master https://github.com/pfaffelh/journal.git
git clone https://github.com/pfaffelh/probability-game.git
git clone https://github.com/leanprover-community/repl.git
~/lean/probability-game/server/deploy.sh --start
```

After that, `~/lean/probability-game/server/deploy.sh` brings the server to the newest commits of
all three branches (`show`, `main`, `monad`, see `BRANCHES.md`), served at `/show/`, `/main/`,
`/monad/`.
`journalctl --user -u probgame-bridge -f` shows what Lean is asked (a line per request).

## The sandbox

Each REPL runs in `bwrap --unshare-all`: no network, its own processes, and a file system that is
read-only and shows only `/usr`, the Lean toolchain, the journal and the REPL, with a `/tmp` of
64 MB. Lean code from visitors (`#eval` with IO, `run_tac`) can neither reach out nor read the
home directory. A request may take `TIMEOUT` seconds (then the REPL is restarted), a REPL
`MEMORY_GB` (then it is killed), and the bridge accepts only the game's own contexts (`ALLOWED`).
