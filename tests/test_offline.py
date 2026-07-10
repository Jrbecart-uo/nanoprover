"""
Offline smoke tests -- no Lean toolchain, no network, no API key.
Run:  python tests/test_offline.py
"""

import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FAILURES = []


def check(name, ok, detail=""):
    print("  [{}] {} {}".format("ok" if ok else "FAIL", name, detail))
    if not ok:
        FAILURES.append(name)


def run(args, cwd=ROOT):
    p = subprocess.run([sys.executable] + args, cwd=cwd,
                       capture_output=True, text=True, timeout=120)
    return p.returncode, p.stdout + p.stderr


print("== imports ==")
sys.path.insert(0, os.path.join(ROOT, "core"))
try:
    import proof_env, agents, search  # noqa: F401
    check("core modules import", True)
except Exception as e:
    check("core modules import", False, str(e))

print("== sandbox unit checks ==")
from proof_env import MockEnv, Solved, Progress, Failed  # noqa: E402

env = MockEnv()
s0 = env.initial_state()
check("mock: valid rewrite progresses",
      isinstance(env.apply(s0, "rw a + b->S1"), Progress))
check("mock: invalid rule rejected",
      isinstance(env.apply(s0, "rw a + b->WRONG"), Failed))
check("mock: inapplicable lhs rejected",
      isinstance(env.apply(s0, "rw S2->SUM"), Failed))

print("== propositional PoC (forward chaining) ==")
code, out = run(["prop_poc/agent_solver_loop.py", "--no-llm"])
check("prop_poc solves A->D", code == 0 and "VICTORY" in out)

print("== core mock search (best-first backward) ==")
code, out = run(["run.py", "--mock", "--no-claude"],
                cwd=os.path.join(ROOT, "core"))
check("mock search finds proof", code == 0 and "PROOF FOUND" in out)

print()
if FAILURES:
    print("FAILED: {}".format(", ".join(FAILURES)))
    sys.exit(1)
print("all offline tests passed")
