#!/usr/bin/env python3
"""Persistent Lean REPL server for nanoprover.

Boots leanprover-community/repl inside the mathlib4 env, runs `import Mathlib`
once (~1 min), then serves proof checks over a unix socket in ~1s each,
returning real goal states and proofState ids for tactic-by-tactic stepping.

Usage:
  repl.py start [--imports "Mathlib"]   daemonize the server (idempotent)
  repl.py status                        readiness, base env, uptime
  repl.py stop                          kill server + Lean process tree
  repl.py check FILE|- [--env N]        check a .lean file (or stdin)
  repl.py code "CODE" [--env N]         check an inline snippet
  repl.py tactic N "TAC"                run a tactic against proofState N
  repl.py raw '{"cmd": ...}'            send raw REPL JSON

check/code print PASS/FAIL first, then the REPL's JSON verbatim (goals,
sorries, messages). A `sorry` is always FAIL. Commands run against the
pre-imported base env by default, so snippets need no import line.
"""

import argparse
import json
import os
import socket
import subprocess
import sys
import time

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MATHLIB = os.path.join(REPO, "mathlib4")
REPL_BIN = os.path.join(REPO, "repl", ".lake", "build", "bin", "repl")
RUN_DIR = os.path.join(REPO, ".repl")
SOCK = os.path.join(RUN_DIR, "repl.sock")
PIDFILE = os.path.join(RUN_DIR, "daemon.pid")
LOG = os.path.join(RUN_DIR, "daemon.log")
STATE = os.path.join(RUN_DIR, "state.json")
LEMMAS = os.path.join(REPO, "lemmas.lean")

DEFAULT_IMPORTS = "Mathlib"
REQUEST_TIMEOUT = 300  # seconds per REPL command before restart


def log(msg):
    with open(LOG, "a") as f:
        f.write(f"[{time.strftime('%H:%M:%S')}] {msg}\n")


# ---------------------------------------------------------------- REPL child

class Repl:
    """One repl subprocess. Speaks newline-JSON-blank-line framing."""

    def __init__(self, imports):
        self.imports = imports
        self.proc = None
        self.base_env = None
        self.boot_seconds = None
        self.lines = None  # queue fed by reader thread

    def start(self):
        import queue
        import threading
        env = dict(os.environ)
        env["PATH"] = os.path.expanduser("~/.elan/bin") + ":" + env.get("PATH", "")
        self.proc = subprocess.Popen(
            ["lake", "env", REPL_BIN],
            cwd=MATHLIB, env=env, text=True,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL, start_new_session=True,
        )
        # NEVER select() on proc.stdout: readline buffers past the kernel fd,
        # so select starves on data already sitting in the userspace buffer.
        self.lines = queue.Queue()
        threading.Thread(target=self._reader, daemon=True).start()
        t0 = time.time()
        imports = " ".join("import " + m for m in self.imports.split())
        resp = self.request({"cmd": imports}, timeout=900)
        if "env" not in resp:
            raise RuntimeError(f"import failed: {resp}")
        self.base_env = resp["env"]
        self.boot_seconds = round(time.time() - t0, 1)
        log(f"booted in {self.boot_seconds}s, base env {self.base_env}")

    def _reader(self):
        for line in self.proc.stdout:
            self.lines.put(line)
        self.lines.put(None)  # EOF sentinel

    def request(self, obj, timeout=REQUEST_TIMEOUT):
        """Send one JSON command, read one JSON response (ends at blank line)."""
        import queue
        self.proc.stdin.write(json.dumps(obj) + "\n\n")
        self.proc.stdin.flush()
        buf, deadline = [], time.time() + timeout
        while True:
            remaining = deadline - time.time()
            if remaining <= 0:
                raise TimeoutError(f"no response after {timeout}s")
            try:
                line = self.lines.get(timeout=min(remaining, 5))
            except queue.Empty:
                if self.proc.poll() is not None:
                    raise RuntimeError("repl process died")
                continue
            if line is None:
                raise RuntimeError("repl closed stdout")
            if line.strip() == "":
                if buf:
                    return json.loads("".join(buf))
                continue
            buf.append(line)

    def kill(self):
        if self.proc and self.proc.poll() is None:
            try:
                os.killpg(os.getpgid(self.proc.pid), 9)
            except ProcessLookupError:
                pass


# ------------------------------------------------------------------- server

def _load_lemmas(repl):
    """Elaborate lemmas.lean into a dedicated env; None if absent/broken."""
    if not os.path.exists(LEMMAS):
        return None
    src = "\n".join(l for l in open(LEMMAS).read().splitlines()
                    if not l.strip().startswith("import "))
    try:
        resp = repl.request({"cmd": src, "env": repl.base_env}, timeout=600)
        if any(m["severity"] == "error" for m in resp.get("messages", [])):
            log(f"lemmas.lean has errors, not loading: {resp['messages'][:1]}")
            return None
        log(f"lemmas.lean loaded as env {resp['env']}")
        return resp["env"]
    except (TimeoutError, RuntimeError) as e:
        log(f"lemmas.lean load failed: {e}")
        return None


def serve(imports):
    os.makedirs(RUN_DIR, exist_ok=True)
    repl = Repl(imports)
    log("booting lean repl...")
    _write_state({"ready": False, "phase": "importing", "pid": os.getpid(),
                  "imports": imports, "started": time.time()})
    repl.start()
    _write_state({"ready": True, "base_env": repl.base_env,
                  "lemmas_env": _load_lemmas(repl), "pid": os.getpid(),
                  "imports": imports, "boot_seconds": repl.boot_seconds,
                  "started": time.time()})

    if os.path.exists(SOCK):
        os.unlink(SOCK)
    srv = socket.socket(socket.AF_UNIX)
    srv.bind(SOCK)
    srv.listen(4)
    log("serving on " + SOCK)

    while True:
        conn, _ = srv.accept()
        try:
            data = b""
            while not data.endswith(b"\n"):
                chunk = conn.recv(65536)
                if not chunk:
                    break
                data += chunk
            req = json.loads(data.decode())
            if req.get("op") == "shutdown":
                try:
                    conn.sendall(b'{"ok": true}\n')
                except OSError:
                    pass
                conn.close()
                break
            cmd = req["cmd"]
            if "env" not in cmd and "cmd" in cmd and "proofState" not in cmd:
                cmd["env"] = repl.base_env
            try:
                resp = repl.request(cmd, timeout=req.get("timeout", REQUEST_TIMEOUT))
            except (TimeoutError, RuntimeError) as e:
                log(f"repl error ({e}); restarting")
                repl.kill()
                _write_state({"ready": False, "phase": "re-importing",
                              "pid": os.getpid(), "imports": imports,
                              "started": time.time()})
                repl = Repl(imports)
                repl.start()
                _write_state({"ready": True, "base_env": repl.base_env,
                              "lemmas_env": _load_lemmas(repl),
                              "pid": os.getpid(), "imports": imports,
                              "boot_seconds": repl.boot_seconds,
                              "started": time.time()})
                resp = {"error": f"{e}; repl restarted, envs/proofStates lost"}
            conn.sendall((json.dumps(resp) + "\n").encode())
        except Exception as e:
            log(f"client error: {e}")
            try:
                conn.sendall((json.dumps({"error": str(e)}) + "\n").encode())
            except OSError:
                pass
        finally:
            conn.close()

    repl.kill()
    srv.close()
    os.unlink(SOCK)
    os.unlink(PIDFILE)
    log("shut down")


def _write_state(d):
    with open(STATE, "w") as f:
        json.dump(d, f)


def daemonize(imports):
    if _ping() is not None:
        print("already running")
        return
    os.makedirs(RUN_DIR, exist_ok=True)
    if os.fork() > 0:
        return
    os.setsid()
    if os.fork() > 0:
        os._exit(0)
    with open(PIDFILE, "w") as f:
        f.write(str(os.getpid()))
    devnull = os.open(os.devnull, os.O_RDWR)
    logfd = os.open(LOG, os.O_WRONLY | os.O_CREAT | os.O_APPEND)
    os.dup2(devnull, 0)
    os.dup2(logfd, 1)
    os.dup2(logfd, 2)
    try:
        serve(imports)
    except Exception as e:
        log(f"fatal: {e}")
    os._exit(0)


# ------------------------------------------------------------------- client

def _ping():
    """Return state dict if a live daemon holds the pidfile, else None."""
    try:
        with open(PIDFILE) as f:
            pid = int(f.read().strip())
        os.kill(pid, 0)
        with open(STATE) as f:
            return json.load(f)
    except (FileNotFoundError, ValueError, ProcessLookupError, PermissionError):
        return None


def ask(cmd, timeout=REQUEST_TIMEOUT):
    c = socket.socket(socket.AF_UNIX)
    c.settimeout(timeout + 30)
    c.connect(SOCK)
    c.sendall((json.dumps({"cmd": cmd, "timeout": timeout}) + "\n").encode())
    data = b""
    while not data.endswith(b"\n"):
        chunk = c.recv(65536)
        if not chunk:
            break
        data += chunk
    c.close()
    return json.loads(data.decode())


def verdict(resp):
    """PASS iff no errors and no sorries (and, for tactic mode, no open goals)."""
    if "error" in resp:
        return "ERROR"
    if "Lean error" in resp.get("message", ""):
        return "FAIL"
    if "proofStatus" in resp:  # tactic-mode response
        return "PASS" if resp["proofStatus"].startswith("Completed") else "OPEN GOALS"
    msgs = resp.get("messages", [])
    if any(m["severity"] == "error" for m in msgs):
        return "FAIL"
    if resp.get("sorries") or any("sorry" in m.get("data", "") for m in msgs):
        return "FAIL (sorry)"
    return "PASS"


def print_result(resp):
    print(verdict(resp))
    print(json.dumps(resp, indent=1, ensure_ascii=False))
    sys.exit(0 if verdict(resp) == "PASS" else 1)


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="op", required=True)
    s = sub.add_parser("start")
    s.add_argument("--imports", default=DEFAULT_IMPORTS)
    sub.add_parser("status")
    sub.add_parser("stop")
    for name in ("check", "code"):
        c = sub.add_parser(name)
        c.add_argument("file" if name == "check" else "snippet")
        c.add_argument("--env", type=int, default=None)
        c.add_argument("--lemmas", action="store_true",
                       help="run against the env with lemmas.lean pre-loaded")
        c.add_argument("--timeout", type=int, default=REQUEST_TIMEOUT)
    t = sub.add_parser("tactic")
    t.add_argument("state", type=int)
    t.add_argument("tac")
    r = sub.add_parser("raw")
    r.add_argument("json")
    a = p.parse_args()

    if a.op == "start":
        daemonize(a.imports)
        print("daemon launched; poll `repl.py status` until ready "
              "(import Mathlib takes ~1-2 min)")
    elif a.op == "status":
        st = _ping()
        if st is None:
            print("not running")
            sys.exit(1)
        st["uptime_s"] = round(time.time() - st.pop("started", time.time()))
        print(json.dumps(st))
        sys.exit(0 if st.get("ready") else 2)
    elif a.op == "stop":
        st = _ping()
        if st is None:
            print("not running")
            return
        try:
            c = socket.socket(socket.AF_UNIX)
            c.settimeout(10)
            c.connect(SOCK)
            c.sendall(b'{"op": "shutdown"}\n')
            c.recv(64)  # wait for ack so the pidfile is gone before we return
            c.close()
            for _ in range(20):
                if _ping() is None:
                    break
                time.sleep(0.5)
            print("stopped")
        except OSError:
            os.kill(st["pid"], 9)
            print("killed")
    elif a.op in ("check", "code"):
        st = _ping()
        if st is None:
            sys.exit("daemon not running; repl.py start")
        if a.op == "check":
            src = sys.stdin.read() if a.file == "-" else open(a.file).read()
        else:
            src = a.snippet
        # base env already has Mathlib; strip import lines to avoid re-elab
        src = "\n".join(l for l in src.splitlines()
                        if not l.strip().startswith("import "))
        cmd = {"cmd": src}
        if a.lemmas:
            if st.get("lemmas_env") is None:
                sys.exit("no lemmas env (lemmas.lean missing/broken at boot)")
            cmd["env"] = st["lemmas_env"]
        if a.env is not None:
            cmd["env"] = a.env
        print_result(ask(cmd, timeout=a.timeout))
    elif a.op == "tactic":
        print_result(ask({"tactic": a.tac, "proofState": a.state}))
    elif a.op == "raw":
        print_result(ask(json.loads(a.json)))


if __name__ == "__main__":
    main()
