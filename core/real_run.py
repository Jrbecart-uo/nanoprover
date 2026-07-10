"""
End-to-end demo against the REAL Lean 4 kernel via LeanCLIEnv + the builtin
tactic agent. No LLM required (runs with zero API credentials), no full
LeanDojo trace required. Proves the two theorems from the lean4-example repo.
"""
import os
from lean_cli_env import LeanCLIEnv
from agents import BuiltinAgent, PortfolioAgent
from search import search

REPO = os.environ.get("NANOPROVER_LEAN_DIR",
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lean4-example"))

THEOREMS = [
    {"name": "foo",         "sig": "(a : Nat) : a + 1 = Nat.succ a",       "preamble": ""},
    {"name": "hello_world", "sig": "(a b c : Nat) : a + b + c = a + c + b", "preamble": ""},
]

def main():
    agent = PortfolioAgent([BuiltinAgent()])
    print("Portfolio: builtin (real Lean kernel; no LLM)\n")
    all_ok = True
    for t in THEOREMS:
        print("=" * 62)
        print("THEOREM {}:  {}".format(t["name"], t["sig"]))
        env = LeanCLIEnv(signature=t["sig"], preamble=t["preamble"], cwd=REPO)
        # branching >= number of builtins so every candidate is tried in one expand
        result = search(env, agent, branching=12, max_expansions=3, verbose=True)
        all_ok = all_ok and result.solved
    print("=" * 62)
    print("ALL PROVED" if all_ok else "some unproved")
    return 0 if all_ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
