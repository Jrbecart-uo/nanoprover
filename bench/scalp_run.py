"""Fast scalp driver: preflight + one batched kernel call per round."""
import argparse, json, os, sys, time
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "core")); sys.path.insert(0, os.path.join(ROOT, "bench"))
from scalp import preflight, check_batch

ap = argparse.ArgumentParser()
ap.add_argument("--bench", choices=["putnam", "minif2f"], default="putnam")
ap.add_argument("--name", required=True); ap.add_argument("--scripts", required=True)
a = ap.parse_args()
mod = __import__(a.bench)
g = next(p for p in mod.parse_problems() if p["name"] == a.name)
pre = "import Mathlib\nset_option maxHeartbeats 800000"
if g["open"]: pre += "\nopen " + g["open"]
scripts = json.load(open(a.scripts))
print("GOAL {}:\n  {}\n".format(a.name, g["sig"][:200]))

t0 = time.time()
ok_scripts, skipped = [], 0
for i, s in enumerate(scripts):
    missing = preflight(s)
    if missing:
        print("  [preflight] candidate {} SKIPPED, unknown names: {}".format(i+1, missing))
        skipped += 1
    else:
        ok_scripts.append((i, s))
print("  preflight: {}/{} candidates pass ({}ms)".format(
    len(ok_scripts), len(scripts), int((time.time()-t0)*1000)))

if ok_scripts:
    results, dt = check_batch(g["sig"], pre, [s for _, s in ok_scripts])
    print("  kernel batch: {} candidates in {}s (one import)".format(len(ok_scripts), dt))
    for (i, s), (solved, err) in zip(ok_scripts, results):
        if solved:
            print("\n*** candidate {} ACCEPTED ***".format(i+1))
            print(s); sys.exit(0)
        print("  candidate {}: {}".format(i+1, err.splitlines()[0][:150]))
print("\nno candidate accepted"); sys.exit(1)
