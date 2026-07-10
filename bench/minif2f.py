"""
External benchmark: miniF2F (Lean 4) test split -- competition problems we did
NOT author, with published baselines in the literature.

Statements are parsed from miniF2F-lean4/MiniF2F/Test/*.lean and re-checked
against OUR mathlib checkout. For speed, probes are BATCHED: one lean file per
chunk of goals carries, for every goal, a `sorry` control variant (does the
statement even elaborate on our mathlib version?) plus one variant per builtin
tactic. One `import Mathlib` amortizes across the whole chunk; verdicts are
recovered from error line numbers.

    python bench/minif2f.py --n 24 --chunk-size 4 --chunks 0-2
    python bench/minif2f.py --aggregate            # combine chunk JSONs
"""

import argparse
import glob
import json
import os
import re
import subprocess
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MINIF2F = os.path.join(ROOT, "miniF2F-lean4", "MiniF2F", "Test")
MATHLIB = os.environ.get("NANOPROVER_MATHLIB_DIR", os.path.join(ROOT, "mathlib4"))

TACTICS = ["norm_num", "simp", "omega", "linarith", "nlinarith",
           "positivity", "exact?"]

STMT_RE = re.compile(
    r"theorem\s+(\S+)([\s\S]*?):=\s*by\s+sorry\s*$", re.MULTILINE)
OPEN_RE = re.compile(r"^open\s+(.+)$", re.MULTILINE)


def parse_problems():
    problems = []
    for path in sorted(glob.glob(os.path.join(MINIF2F, "*.lean"))):
        src = open(path).read()
        src = re.sub(r"/-[\s\S]*?-/", "", src)          # strip block comments
        m = STMT_RE.search(src)
        if not m:
            continue
        opens = OPEN_RE.search(src)
        problems.append({
            "name": m.group(1),
            "sig": " ".join(m.group(2).split()),         # binders + goal, one line
            "open": opens.group(1).strip() if opens else "",
        })
    return problems


def select(problems, n):
    """Every k-th problem for category spread (aime/algebra/amc/mathd/...)."""
    k = max(1, len(problems) // n)
    return problems[::k][:n]


def build_chunk(goals):
    """One lean file: per goal a sorry-control + one variant per tactic.
    Returns (source, linemap) where linemap[(gi, label)] = (start, end) lines."""
    lines = ["import Mathlib", "set_option maxHeartbeats 400000", ""]
    linemap = {}
    for gi, g in enumerate(goals):
        variants = [("sorry", "sorry")] + [(t, t) for t in TACTICS]
        for label, tac in variants:
            prefix = "open {} in".format(g["open"]) if g["open"] else None
            start = len(lines) + 1
            if prefix:
                lines.append(prefix)
            # `example`, not `theorem`: named declarations (even failed or
            # sorry'd ones) enter the environment, and exact? would happily
            # cite a sibling variant of the SAME statement. Anonymous
            # examples leave nothing to cite.
            lines.append("example {} := by".format(g["sig"]))
            lines.append("  " + tac)
            lines.append("")
            linemap[(gi, label)] = (start, len(lines))
    return "\n".join(lines) + "\n", linemap


def run_chunk(goals, timeout=560):
    src, linemap = build_chunk(goals)
    path = "/tmp/minif2f_chunk_probe.lean"
    with open(path, "w") as f:
        f.write(src)
    t0 = time.time()
    p = subprocess.run(["lake", "env", "lean", path], cwd=MATHLIB,
                       capture_output=True, text=True, timeout=timeout)
    dt = time.time() - t0
    # collect error line numbers
    err_lines = set()
    for m in re.finditer(r"probe\.lean:(\d+):\d+: error", p.stdout + p.stderr):
        err_lines.add(int(m.group(1)))

    def has_error(gi, label):
        s, e = linemap[(gi, label)]
        return any(s <= ln <= e for ln in err_lines)

    results = []
    for gi, g in enumerate(goals):
        usable = not has_error(gi, "sorry")
        solved_by = [t for t in TACTICS if not has_error(gi, t)] if usable else []
        results.append({"name": g["name"], "usable": usable,
                        "solved_by": solved_by, "solved": bool(solved_by)})
    return results, round(dt, 1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=24)
    ap.add_argument("--chunk-size", type=int, default=4)
    ap.add_argument("--chunks", default=None, help="e.g. 0-2 or 3-5")
    ap.add_argument("--aggregate", action="store_true")
    args = ap.parse_args()

    if args.aggregate:
        allr = []
        for f in sorted(glob.glob("/tmp/minif2f_results_*.json")):
            allr += json.load(open(f))
        usable = [r for r in allr if r["usable"]]
        solved = [r for r in usable if r["solved"]]
        print("problems attempted: {}   usable on our mathlib: {}   solved: {}"
              .format(len(allr), len(usable), len(solved)))
        if usable:
            print("BUILTIN SOLVE RATE on miniF2F sample: {}/{} = {:.0f}%".format(
                len(solved), len(usable), 100 * len(solved) / len(usable)))
        wins = {}
        for r in solved:
            wins[r["solved_by"][0]] = wins.get(r["solved_by"][0], 0) + 1
        print("first-tactic wins:", wins)
        print("unsolved:", [r["name"] for r in usable if not r["solved"]])
        return

    problems = select(parse_problems(), args.n)
    chunks = [problems[i:i + args.chunk_size]
              for i in range(0, len(problems), args.chunk_size)]
    lo, hi = (map(int, args.chunks.split("-")) if args.chunks
              else (0, len(chunks) - 1))
    for ci in range(lo, hi + 1):
        results, dt = run_chunk(chunks[ci])
        out = "/tmp/minif2f_results_{}.json".format(ci)
        json.dump(results, open(out, "w"), indent=1)
        for r in results:
            print("  [{}] {:44s} {}".format(
                ci, r["name"],
                "SOLVED via " + r["solved_by"][0] if r["solved"]
                else ("--" if r["usable"] else "UNUSABLE")))
        print("chunk {} done in {}s -> {}".format(ci, dt, out))


if __name__ == "__main__":
    main()
