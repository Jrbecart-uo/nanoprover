"""
Run the error-feedback retry loop on a miniF2F goal.

    python bench/retry_run.py --name mathd_numbertheory_353 --scripts att.json
    python bench/retry_run.py --name ... --interactive          # human in loop
    python bench/retry_run.py --name ... --claude               # needs API key

att.json is a JSON list of scripts (tried in order, each informed by the
previous error when a live proposer is driving).
"""

import argparse
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "core"))
sys.path.insert(0, os.path.join(ROOT, "bench"))

from lean_cli_env import LeanCLIEnv
from retry import (propose_with_feedback, ScriptedProposer,
                   InteractiveProposer, ClaudeRetryProposer)
from minif2f import parse_problems, MATHLIB


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--name", required=True)
    ap.add_argument("--scripts", help="JSON list of attempts")
    ap.add_argument("--interactive", action="store_true")
    ap.add_argument("--claude", action="store_true")
    ap.add_argument("--max-rounds", type=int, default=5)
    args = ap.parse_args()

    g = next((p for p in parse_problems() if p["name"] == args.name), None)
    if g is None:
        sys.exit("unknown problem: " + args.name)

    preamble = "import Mathlib\nset_option maxHeartbeats 800000"
    if g["open"]:
        preamble += "\nopen " + g["open"]
    env = LeanCLIEnv(signature=g["sig"], preamble=preamble,
                     lean_cmd=["lake", "env", "lean"], cwd=MATHLIB, timeout=180)

    if args.claude:
        proposer = ClaudeRetryProposer()
    elif args.interactive:
        proposer = InteractiveProposer()
    else:
        proposer = ScriptedProposer(json.load(open(args.scripts)))

    print("GOAL {}:\n  {}\n".format(args.name, g["sig"]))
    r = propose_with_feedback(env, proposer, max_rounds=args.max_rounds)
    print("\n{} after {} round(s)".format("SOLVED" if r.solved else "unsolved",
                                          r.rounds))
    if r.solved:
        print("accepted script:\n" + r.script)
    return 0 if r.solved else 1


if __name__ == "__main__":
    sys.exit(main())
