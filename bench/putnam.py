"""
PutnamBench baseline -- the successor benchmark to miniF2F (harder; current
research systems solve only a small fraction).

We run the PURE-PROOF subset (326 of 672): problems with a `..._solution`
abbrev also require producing the answer term, and their official answers sit
in reference comments -- using those would be self-deception, so they're
excluded from the baseline rather than gamed.

Same batched probing as bench/minif2f.py: per chunk one lean file with, per
goal, a sorry-elaboration control + one `example` variant per tactic; one
`import Mathlib` amortized per chunk; verdicts by error line mapping.

    python bench/putnam.py --chunk-size 4 --chunks 0-19
    python bench/putnam.py --aggregate
"""

import argparse
import glob
import json
import os
import re
import subprocess
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PUTNAM = os.path.join(ROOT, "PutnamBench", "lean4", "src")
MATHLIB = os.environ.get("NANOPROVER_MATHLIB_DIR", os.path.join(ROOT, "mathlib4"))

TACTICS = ["norm_num", "simp", "omega", "linarith", "nlinarith",
           "positivity", "exact?"]

# term-mode `:= sorry` (possibly on its own line), unlike miniF2F's `:= by sorry`
STMT_RE = re.compile(r"^theorem\s+(\S+)([\s\S]*?):=\s*(?:by\s+)?sorry\s*$",
                     re.MULTILINE)


def parse_problems():
    problems = []
    for path in sorted(glob.glob(os.path.join(PUTNAM, "*.lean"))):
        src = open(path).read()
        if "_solution" in src:
            continue                      # answer-construction problem: excluded
        src = re.sub(r"/-[\s\S]*?-/", "", src)   # strip doc/block comments
        src = re.sub(r"--.*", "", src)           # strip line comments
        m = STMT_RE.search(src)
        if not m:
            continue
        opens = re.findall(r"^open\s+(.+)$", src, re.MULTILINE)
        problems.append({
            "name": m.group(1),
            "sig": " ".join(m.group(2).split()),
            "open": " ".join(o.strip() for o in opens),
        })
    return problems


def build_chunk(goals):
    lines = ["import Mathlib", "set_option maxHeartbeats 400000", ""]
    linemap = {}
    for gi, g in enumerate(goals):
        for label, tac in [("sorry", "sorry")] + [(t, t) for t in TACTICS]:
            start = len(lines) + 1
            if g["open"]:
                lines.append("open {} in".format(g["open"]))
            # anonymous example: named (even sorry'd) theorems enter the env
            # and exact? would cite a sibling variant (see minif2f.py)
            lines.append("example {} := by".format(g["sig"]))
            lines.append("  " + tac)
            lines.append("")
            linemap[(gi, label)] = (start, len(lines))
    return "\n".join(lines) + "\n", linemap


def run_chunk(goals, ci=0, timeout=560):
    src, linemap = build_chunk(goals)
    path = "/tmp/putnam_probe_{}.lean".format(ci)
    with open(path, "w") as f:
        f.write(src)
    t0 = time.time()
    p = subprocess.run(["lake", "env", "lean", path], cwd=MATHLIB,
                       capture_output=True, text=True, timeout=timeout)
    dt = time.time() - t0
    err_lines = {int(m.group(1)) for m in
                 re.finditer(r"\.lean:(\d+):\d+: error", p.stdout + p.stderr)}

    def bad(gi, label):
        s, e = linemap[(gi, label)]
        return any(s <= ln <= e for ln in err_lines)

    out = []
    for gi, g in enumerate(goals):
        usable = not bad(gi, "sorry")
        solved_by = [t for t in TACTICS if not bad(gi, t)] if usable else []
        out.append({"name": g["name"], "usable": usable,
                    "solved_by": solved_by, "solved": bool(solved_by)})
    return out, round(dt, 1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--chunk-size", type=int, default=4)
    ap.add_argument("--chunks", default=None, help="e.g. 0-19")
    ap.add_argument("--aggregate", action="store_true")
    args = ap.parse_args()

    if args.aggregate:
        allr = []
        for f in sorted(glob.glob("/tmp/putnam_results_*.json")):
            allr += json.load(open(f))
        usable = [r for r in allr if r["usable"]]
        solved = [r for r in usable if r["solved"]]
        print("attempted: {}  usable: {}  solved: {}".format(
            len(allr), len(usable), len(solved)))
        if usable:
            print("BUILTIN SOLVE RATE on PutnamBench (pure-proof subset): "
                  "{}/{} = {:.1f}%".format(len(solved), len(usable),
                                           100 * len(solved) / len(usable)))
        wins = {}
        for r in solved:
            wins[r["solved_by"][0]] = wins.get(r["solved_by"][0], 0) + 1
        print("first-tactic wins:", wins)
        print("solved:", [r["name"] for r in solved])
        return

    problems = parse_problems()
    chunks = [problems[i:i + args.chunk_size]
              for i in range(0, len(problems), args.chunk_size)]
    lo, hi = (map(int, args.chunks.split("-")) if args.chunks
              else (0, len(chunks) - 1))
    for ci in range(lo, min(hi + 1, len(chunks))):
        results, dt = run_chunk(chunks[ci], ci)
        json.dump(results, open("/tmp/putnam_results_{:03d}.json".format(ci), "w"),
                  indent=1)
        for r in results:
            print("  [{}] {:24s} {}".format(
                ci, r["name"],
                "SOLVED via " + r["solved_by"][0] if r["solved"]
                else ("--" if r["usable"] else "UNUSABLE")))
        print("chunk {} done in {}s".format(ci, dt))


if __name__ == "__main__":
    main()
