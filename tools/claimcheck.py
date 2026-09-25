#!/usr/bin/env python3
"""Check a published Lean proof of a claimed result, fast and in a sandbox.

Built from the Navier-Stokes and Hodge audits (verification/NS_AUDIT.md, HODGE_AUDIT.md).
Machine-checkable parts of a claim audit, in one place:

  setup  VER             build landrun, nanoda, and lean4export + comparator for Lean VER
  probe                  sandbox self-test: every escape route must be blocked
  selftest VER           run comparator's own adversarial test projects under the sandbox
  fetch  NAME URL [--rev R]   fresh clone into external/claims/NAME/src (+ mathlib cache)
  build  NAME TARGET...  lake build (one step per claim at a time: lock)
  axioms NAME MODULE DECL...  #print axioms
  surface NAME MODULE ROOT [--prefix P]  repo-local constants the meaning of ROOT depends on
  comparator NAME CONFIG...   comparator in the layered sandbox (+ nanoda if configured)
  status NAME            last lines + completion sentinels of every step log

Steps that can outlive the 10-minute shell cap take --detach: they re-run themselves under
setsid, log to external/claims/NAME/<step>.log, and end with a line
`CLAIMCHECK_DONE <step> rc=<n>` (wait on that line, never on pgrep -f: see KNOWN_TRAPS).

Sandbox (WSL2 kernel 6.6 has Landlock ABI v3; landrun main wants v9): systemd-run seccomp
(no inet/unix sockets, no ptrace/module/... syscalls, NoNewPrivileges) + unshare
(user/net/ipc/pid/uts/mount namespaces) + landrun --best-effort (filesystem rules).
Comparator's guarantee assumes the solution was never built outside the sandbox: for a
comparator run, fetch a fresh clone and do NOT `build` it first.
"""

import argparse
import fcntl
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXT = os.path.join(REPO, "external")
TOOLS = os.path.join(EXT, "tools")
CLAIMS = os.path.join(EXT, "claims")
HOME = os.path.expanduser("~")
PATH = ":".join([f"{HOME}/.elan/bin", f"{HOME}/.local/go/bin", f"{HOME}/.cargo/bin",
                 "/usr/local/bin", "/usr/bin", "/bin"])
ENV = dict(os.environ, PATH=PATH, LEAN_NUM_THREADS=os.environ.get("LEAN_NUM_THREADS", "4"))

SANDBOX = ["systemd-run", "--user", "--wait", "--pipe", "--collect", "-q",
           "--property=RestrictAddressFamilies=AF_NETLINK", "--property=NoNewPrivileges=yes",
           "--property=SystemCallFilter=~@debug @module @reboot @swap @raw-io @clock @cpu-emulation"]
UNSHARE = ["unshare", "--user", "--map-root-user", "--net", "--ipc", "--pid", "--uts",
           "--mount", "--fork", "--mount-proc"]


def sh(cmd, cwd=None, check=True, **kw):
    print("+", " ".join(cmd) if isinstance(cmd, list) else cmd, flush=True)
    r = subprocess.run(cmd, cwd=cwd, env=ENV, **kw)
    if check and r.returncode:
        sys.exit(f"command failed (rc={r.returncode})")
    return r


def sandboxed(argv, cwd, env_extra=None):
    """argv run inside systemd-run seccomp + fresh namespaces (network removed)."""
    env = ["-E", f"PATH={env_extra.get('PATH', PATH) if env_extra else PATH}",
           "-E", f"LEAN_NUM_THREADS={ENV['LEAN_NUM_THREADS']}"]
    for k, v in (env_extra or {}).items():
        if k != "PATH":
            env += ["-E", f"{k}={v}"]
    return SANDBOX + env + ["--working-directory", cwd, "--"] + UNSHARE + argv


def toolchain(project_dir):
    with open(os.path.join(project_dir, "lean-toolchain")) as f:
        return f.read().strip().split(":")[-1]


def tool_bin(ver):
    return os.path.join(TOOLS, f"bin-{ver}")


def claim_dir(name):
    return os.path.join(CLAIMS, name)


class Lock:
    """One heavy step per claim at a time (two concurrent `lake build`s corrupt .lake)."""
    def __init__(self, name):
        os.makedirs(claim_dir(name), exist_ok=True)
        self.f = open(os.path.join(claim_dir(name), ".lock"), "w")

    def __enter__(self):
        try:
            fcntl.flock(self.f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            sys.exit("another claimcheck step holds the lock for this claim; see `status`")
        return self

    def __exit__(self, *a):
        fcntl.flock(self.f, fcntl.LOCK_UN)


def detach(args, step):
    """Re-run this command detached; log + completion sentinel in the claim dir."""
    log = os.path.join(claim_dir(args.name), f"{step}.log")
    argv = [sys.executable, os.path.abspath(__file__)] + [a for a in sys.argv[1:] if a != "--detach"]
    inner = f'{" ".join(map(sh_quote, argv))}; echo "CLAIMCHECK_DONE {step} rc=$?"'
    with open(log, "w") as out:
        subprocess.Popen(["bash", "-c", inner], stdout=out, stderr=subprocess.STDOUT,
                         stdin=subprocess.DEVNULL, start_new_session=True, env=ENV)
    print(f"detached; log: {log}\nwait for: grep -q 'CLAIMCHECK_DONE {step}' {log}")


def sh_quote(s):
    return "'" + s.replace("'", "'\\''") + "'"


# ---------------------------------------------------------------- setup / self-tests

def nearest_tag(url, ver):
    tags = subprocess.run(["git", "ls-remote", "--tags", url], capture_output=True,
                          text=True, env=ENV).stdout
    tags = sorted({t for t in re.findall(r"refs/tags/(v[\w.\-]+)$", tags, re.M)})
    if ver in tags:
        return ver
    mm = re.match(r"(v\d+\.\d+)", ver).group(1)
    same = [t for t in tags if t.startswith(mm + ".")]
    if not same:
        sys.exit(f"no {url} tag near {ver}")
    return max(same, key=lambda t: (("-rc" not in t), t))


def build_versioned(repo_name, url, ver, target):
    d = os.path.join(TOOLS, f"{repo_name}-{ver}")
    if not os.path.isdir(d):
        tag = nearest_tag(url, ver)
        sh(["git", "clone", "-q", "--depth", "1", "--branch", tag, url, d])
        with open(os.path.join(d, "lean-toolchain"), "w") as f:
            f.write(f"leanprover/lean4:{ver}\n")   # must read the target's .olean format
    sh(["lake", "build", target], cwd=d)
    return d


def cmd_setup(a):
    ver = a.ver
    os.makedirs(TOOLS, exist_ok=True)
    lr = os.path.join(TOOLS, "landrun")
    if not os.path.exists(os.path.join(lr, "landrun")):
        if not os.path.isdir(lr):
            sh(["git", "clone", "-q", "https://github.com/Zouuup/landrun", lr])
        sh(["go", "build", "-o", "landrun", "./cmd/landrun"], cwd=lr)
    nd = os.path.join(TOOLS, "nanoda_lib")
    if not os.path.exists(os.path.join(nd, "target/release/nanoda_bin")):
        if not os.path.isdir(nd):
            sh(["git", "clone", "-q", "https://github.com/ammkrn/nanoda_lib", nd])
        sh(["cargo", "build", "--release"], cwd=nd)
    le = build_versioned("lean4export", "https://github.com/leanprover/lean4export", ver, "lean4export")
    co = build_versioned("comparator", "https://github.com/leanprover/comparator", ver, "comparator")
    b = tool_bin(ver)
    os.makedirs(b, exist_ok=True)
    with open(os.path.join(b, "landrun"), "w") as f:
        f.write(f'#!/bin/sh\n# Landlock ABI v3 here: keep filesystem rules, drop the rest\n'
                f'exec {lr}/landrun --best-effort "$@"\n')
    os.chmod(os.path.join(b, "landrun"), 0o755)
    for link, target in [("lean4export", f"{le}/.lake/build/bin/lean4export"),
                         ("nanoda_bin", f"{nd}/target/release/nanoda_bin"),
                         ("comparator", f"{co}/.lake/build/bin/comparator")]:
        p = os.path.join(b, link)
        if os.path.lexists(p):
            os.remove(p)
        os.symlink(target, p)
    print(f"tools for {ver} in {b}")


PROBE = r'''
import os, socket, sys
out = sys.argv[1]; victim = int(sys.argv[2]); outside = sys.argv[3]
def t(name, f):
    try: f(); print(f"ESCAPE {name}")
    except Exception as e: print(f"blocked {name}: {type(e).__name__}")
t("tcp-connect", lambda: socket.create_connection(("1.1.1.1", 443), timeout=3))
t("af_unix", lambda: socket.socket(socket.AF_UNIX))
t("af_inet", lambda: socket.socket(socket.AF_INET))
t("signal-outside-pid", lambda: os.kill(victim, 0))
t("write-outside", lambda: open(outside, "w"))
open(os.path.join(out, "ok"), "w").write("ok")
print("allowed write-inside")
'''


def cmd_probe(a):
    lr = os.path.join(TOOLS, "landrun", "landrun")
    with tempfile.TemporaryDirectory(dir=EXT) as tmp:
        rw = os.path.join(tmp, "rw"); os.mkdir(rw)
        script = os.path.join(tmp, "probe.py")
        open(script, "w").write(PROBE)
        victim = subprocess.Popen(["sleep", "60"])
        outside = os.path.join(tmp, "escaped")
        argv = [lr, "--best-effort", "--rox", "/usr,/lib,/lib64,/bin", "--ro", "/", "--rw", rw,
                "--", "/usr/bin/python3", script, rw, str(victim.pid), outside]
        r = subprocess.run(sandboxed(argv, tmp), capture_output=True, text=True, env=ENV)
        victim.kill()
        lines = [l for l in r.stdout.splitlines() if l.startswith(("ESCAPE", "blocked", "allowed"))]
        print("\n".join(lines))
        bad = [l for l in lines if l.startswith("ESCAPE")] or os.path.exists(outside)
        if bad or not any(l.startswith("allowed") for l in lines):
            sys.exit("PROBE FAILED: sandbox leaks or does not run")
        print("PROBE OK: all escape routes blocked, granted dir writable")


def cmd_selftest(a):
    ver = a.ver
    co_dir = os.path.join(TOOLS, f"comparator-{ver}")
    b = tool_bin(ver)
    comp = os.path.join(b, "comparator")
    if not os.path.exists(comp):
        sys.exit(f"run `setup {ver}` first")
    root = os.path.join(CLAIMS, f"_selftest-{ver}")
    shutil.rmtree(root, ignore_errors=True)
    os.makedirs(root)
    results = []
    for proj in sorted(os.listdir(os.path.join(co_dir, "tests", "projects"))):
        src = os.path.join(co_dir, "tests", "projects", proj)
        dst = os.path.join(root, proj)
        shutil.copytree(src, dst)
        with open(os.path.join(dst, "lean-toolchain"), "w") as f:
            f.write(f"leanprover/lean4:{ver}\n")
        if not os.path.exists(os.path.join(dst, "lakefile.toml")):
            open(os.path.join(dst, "lakefile.toml"), "w").write(
                'name = "comparatortest"\nversion = "0.1.0"\n'
                '[[lean_lib]]\nname = "Solution"\n[[lean_lib]]\nname = "Challenge"\n')
        want = json.load(open(os.path.join(dst, "test.json")))["exit_code"]
        r = subprocess.run(sandboxed(["lake", "env", comp, "config.json"], dst,
                                     {"PATH": f"{b}:{PATH}"}),
                           capture_output=True, text=True, env=ENV)
        rc = r.returncode
        open(os.path.join(dst, "comparator.log"), "w").write(r.stdout + r.stderr)
        ok = (rc == 0) == (want == 0)
        results.append((proj, want, rc, ok))
        print(f"{'ok ' if ok else 'BAD'} {proj}: expected {want}, got {rc}", flush=True)
    bad = [p for p in results if not p[3]]
    print(f"{len(results) - len(bad)}/{len(results)} comparator self-tests agree")
    if bad:
        sys.exit(1)


# ---------------------------------------------------------------- per-claim steps

def src_dir(name):
    d = os.path.join(claim_dir(name), "src")
    if not os.path.isdir(d):
        sys.exit(f"no claim {name}; run fetch")
    return d


def cmd_fetch(a):
    d = os.path.join(claim_dir(a.name), "src")
    if os.path.exists(d):
        sys.exit(f"{d} exists; comparator needs a pristine clone — pick a new NAME")
    os.makedirs(claim_dir(a.name), exist_ok=True)
    sh(["git", "clone", "-q", a.url, d])
    if a.rev:
        sh(["git", "checkout", "-q", a.rev], cwd=d)
    rev = subprocess.run(["git", "rev-parse", "HEAD"], cwd=d, capture_output=True, text=True).stdout.strip()
    meta = {"url": a.url, "rev": rev, "toolchain": toolchain(d)}
    json.dump(meta, open(os.path.join(claim_dir(a.name), "meta.json"), "w"), indent=1)
    print(meta)
    if os.path.exists(os.path.join(d, "lake-manifest.json")) and "mathlib" in open(os.path.join(d, "lake-manifest.json")).read():
        sh(["lake", "exe", "cache", "get"], cwd=d)


def cmd_build(a):
    if a.detach:
        return detach(a, "build")
    with Lock(a.name):
        r = sh(["lake", "build"] + a.targets, cwd=src_dir(a.name), check=False)
        sys.exit(r.returncode)


def lean_file(name, fname, body):
    p = os.path.join(claim_dir(name), fname)   # outside src: keep the clone pristine
    open(p, "w").write(body)
    return p


def cmd_axioms(a):
    body = f"import {a.module}\n" + "".join(f"#print axioms {d}\n" for d in a.decls)
    p = lean_file(a.name, "axioms.lean", body)
    r = subprocess.run(["lake", "env", "lean", p], cwd=src_dir(a.name), capture_output=True,
                       text=True, env=ENV)
    out = r.stdout + r.stderr
    print(out)
    std = {"propext", "Classical.choice", "Quot.sound"}
    extra = set()
    for m in re.finditer(r"depends on axioms: \[([^\]]*)\]", out):
        extra |= {x.strip() for x in m.group(1).split(",")} - std
    if r.returncode:
        sys.exit("lean failed")
    if extra or "sorryAx" in out:
        sys.exit(f"NONSTANDARD AXIOMS: {sorted(extra)}")
    print("axioms OK (standard three only)")


SURFACE = r'''import {module}
open Lean
partial def collect (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {{}}
  let mut stack := #[root]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut refs := ci.type.getUsedConstants
    match ci with
    | .thmInfo _ => pure ()
    | _ => if let some v := ci.value? (allowOpaque := true) then refs := refs ++ v.getUsedConstants
    if let .inductInfo ii := ci then refs := refs ++ ii.ctors.toArray
    for r in refs do
      if !seen.contains r then stack := stack.push r
  return seen
def kindOf : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "AXIOM" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"
run_cmd do
  let env ← Lean.getEnv
  for n in (collect env `{root}).toList do
    let some ci := env.find? n | continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if (`{prefix}).isPrefixOf mod && !n.isInternal then
      IO.println s!"{{mod}}\t{{kindOf ci}}\t{{n}}"
'''


def cmd_surface(a):
    prefix = a.prefix or a.module.split(".")[0]
    p = lean_file(a.name, "surface.lean", SURFACE.format(module=a.module, root=a.root, prefix=prefix))
    r = subprocess.run(["lake", "env", "lean", p], cwd=src_dir(a.name), capture_output=True,
                       text=True, env=ENV)
    if r.returncode:
        sys.exit(r.stdout + r.stderr)
    rows = sorted(l.split("\t") for l in r.stdout.splitlines() if l.count("\t") == 2)
    tsv = os.path.join(claim_dir(a.name), "surface.tsv")
    open(tsv, "w").write("".join("\t".join(x) + "\n" for x in rows))
    kinds, mods = {}, {}
    for m, k, _ in rows:
        kinds[k] = kinds.get(k, 0) + 1
        if k != "theorem":
            mods[m] = mods.get(m, 0) + 1
    print(f"{len(rows)} repo-local constants under `{a.root}`: {kinds}")
    print(f"{len(mods)} modules hold definitions to review -> {tsv}")
    for m, c in sorted(mods.items(), key=lambda x: -x[1])[:15]:
        print(f"  {c:4d}  {m}")
    if kinds.get("AXIOM") or kinds.get("opaque"):
        print("WARNING: axioms/opaques on the surface — review each")


def cmd_comparator(a):
    if a.detach:
        return detach(a, "comparator")
    d = src_dir(a.name)
    ver = toolchain(d)
    b = tool_bin(ver)
    comp = os.path.join(b, "comparator")
    if not os.path.exists(comp):
        sys.exit(f"run `setup {ver}` first")
    if os.path.isdir(os.path.join(d, ".lake", "build")) and not a.allow_prebuilt:
        sys.exit("src has a .lake/build: comparator's guarantee needs the solution unbuilt "
                 "outside the sandbox (fresh fetch, or --allow-prebuilt if you built it yourself "
                 "in a trusted way)")
    rc_all = 0
    with Lock(a.name):
        for cfg in a.configs:
            print(f"=== comparator {cfg}", flush=True)
            r = subprocess.run(sandboxed(["lake", "env", comp, cfg], d, {"PATH": f"{b}:{PATH}"}),
                               env=ENV)
            print(f"=== {cfg}: rc={r.returncode}", flush=True)
            rc_all = rc_all or r.returncode
    sys.exit(rc_all)


def cmd_status(a):
    d = claim_dir(a.name)
    if os.path.exists(os.path.join(d, "meta.json")):
        print(open(os.path.join(d, "meta.json")).read())
    for f in sorted(os.listdir(d)):
        if f.endswith(".log"):
            txt = open(os.path.join(d, f), errors="replace").read().replace("\r", "\n")
            done = re.findall(r"CLAIMCHECK_DONE \S+ rc=\d+", txt)
            tail = [l for l in txt.splitlines() if l.strip()][-3:]
            print(f"--- {f}: {done[-1] if done else 'RUNNING (no sentinel yet)'}")
            print("\n".join("    " + l[:160] for l in tail))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sp = ap.add_subparsers(dest="cmd", required=True)
    p = sp.add_parser("setup"); p.add_argument("ver"); p.set_defaults(f=cmd_setup)
    p = sp.add_parser("probe"); p.set_defaults(f=cmd_probe)
    p = sp.add_parser("selftest"); p.add_argument("ver"); p.set_defaults(f=cmd_selftest)
    p = sp.add_parser("fetch"); p.add_argument("name"); p.add_argument("url")
    p.add_argument("--rev"); p.set_defaults(f=cmd_fetch)
    p = sp.add_parser("build"); p.add_argument("name"); p.add_argument("targets", nargs="+")
    p.add_argument("--detach", action="store_true"); p.set_defaults(f=cmd_build)
    p = sp.add_parser("axioms"); p.add_argument("name"); p.add_argument("module")
    p.add_argument("decls", nargs="+"); p.set_defaults(f=cmd_axioms)
    p = sp.add_parser("surface"); p.add_argument("name"); p.add_argument("module")
    p.add_argument("root"); p.add_argument("--prefix"); p.set_defaults(f=cmd_surface)
    p = sp.add_parser("comparator"); p.add_argument("name"); p.add_argument("configs", nargs="+")
    p.add_argument("--detach", action="store_true"); p.add_argument("--allow-prebuilt", action="store_true")
    p.set_defaults(f=cmd_comparator)
    p = sp.add_parser("status"); p.add_argument("name"); p.set_defaults(f=cmd_status)
    a = ap.parse_args()
    a.f(a)


if __name__ == "__main__":
    main()
