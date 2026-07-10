"""Retry loop on a PutnamBench goal (same as retry_run.py but for putnam.py)."""
import argparse, json, os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "core")); sys.path.insert(0, os.path.join(ROOT, "bench"))
from lean_cli_env import LeanCLIEnv
from retry import propose_with_feedback, ScriptedProposer
from putnam import parse_problems, MATHLIB

ap = argparse.ArgumentParser()
ap.add_argument("--name", required=True); ap.add_argument("--scripts", required=True)
ap.add_argument("--max-rounds", type=int, default=4)
a = ap.parse_args()
g = next(p for p in parse_problems() if p["name"] == a.name)
pre = "import Mathlib\nset_option maxHeartbeats 800000"
if g["open"]: pre += "\nopen " + g["open"]
env = LeanCLIEnv(signature=g["sig"], preamble=pre,
                 lean_cmd=["lake", "env", "lean"], cwd=MATHLIB, timeout=240)
print("GOAL {}:\n  {}\n".format(a.name, g["sig"]))
r = propose_with_feedback(env, ScriptedProposer(json.load(open(a.scripts))), max_rounds=a.max_rounds)
print("\n{} after {} rounds".format("SOLVED" if r.solved else "unsolved", r.rounds))
if r.solved: print(r.script)
sys.exit(0 if r.solved else 1)
