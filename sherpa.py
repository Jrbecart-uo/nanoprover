"""
Turn-by-turn theorem proving against the REAL Lean 4 kernel -- you are the
intuition engine. No API key, no LeanDojo trace.

Each turn: you see the current proof goal, you type a Lean tactic, and the
kernel checks it. Accepted tactics accumulate; the kernel prints the new goal
(Lean reports the remaining goal on an "unsolved goals" error, which we parse
and show). When no goals remain, the theorem is proved.

Commands:
  :undo     drop the last accepted tactic
  :reset    start the proof over
  :proof    show the tactic sequence so far
  :goal     re-print the current goal
  :quit     exit

Run (from mathTest/, with the venv active and elan on PATH):
  source .venv/bin/activate
  export PATH="$HOME/.elan/bin:$PATH"
  python lean_solver/interactive.py                 # default: hello_world
  python lean_solver/interactive.py --theorem foo
"""

import argparse
import os
import subprocess
import sys
import tempfile

REPO = os.environ.get("NANOPROVER_LEAN_DIR",
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean4-example"))

# A couple of ready-made targets from the lean4-example repo.
THEOREMS = {
    "hello_world": {
        "sig": "(a b c : Nat) : a + b + c = a + c + b",
        "preamble": "open Nat (add_assoc add_comm)",
        "hint": "try: rw [add_assoc]  then  rw [add_comm b]  then  rw [←add_assoc]",
    },
    "foo": {
        "sig": "(a : Nat) : a + 1 = Nat.succ a",
        "preamble": "",
        "hint": "try: rfl",
    },
}


def run_lean(preamble, sig, tactics, timeout=30.0):
    """
    Typecheck `theorem __probe__ <sig> := by <tactics>` and classify the result.
    Returns (status, detail) where status is 'solved' | 'goals' | 'error'.
    A body of `skip` (when tactics is empty) surfaces the initial goal.
    """
    body_tactics = tactics if tactics else ["skip"]
    body = "{}\ntheorem __probe__ {} := by\n{}\n".format(
        preamble, sig, "\n".join("  " + t for t in body_tactics))
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(body)
        path = f.name
    try:
        proc = subprocess.run(["lean", path], cwd=REPO,
                              capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "error", "lean timed out"
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass

    out = (proc.stdout + proc.stderr)
    if proc.returncode == 0 and not proc.stderr.strip():
        return "solved", ""
    if "unsolved goals" in out:
        # Everything after the "unsolved goals" marker is the goal state.
        idx = out.find("unsolved goals")
        goal = out[idx + len("unsolved goals"):].strip()
        # Trim any trailing secondary error blocks.
        goal = goal.split("\nerror:")[0].rstrip()
        return "goals", goal
    # A genuine tactic error (bad syntax, tactic failed, etc.).
    first = next((l for l in out.splitlines() if "error" in l.lower()),
                 out.strip().splitlines()[0] if out.strip() else "rejected")
    return "error", first.strip()


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--theorem", choices=list(THEOREMS), default="hello_world")
    ap.add_argument("--sig", help="custom theorem signature (overrides --theorem)")
    ap.add_argument("--preamble", default="", help="custom preamble for --sig")
    args = ap.parse_args(argv)

    if args.sig:
        name, sig, preamble, hint = "custom", args.sig, args.preamble, None
    else:
        t = THEOREMS[args.theorem]
        name, sig, preamble, hint = args.theorem, t["sig"], t["preamble"], t["hint"]

    print("=" * 66)
    print("Interactive Lean prover  --  you are the intuition engine")
    print("theorem {} {}".format(name, sig))
    if preamble:
        print("(preamble: {})".format(preamble))
    if hint:
        print(hint)
    print("commands: :undo  :reset  :proof  :goal  :quit")
    print("=" * 66)

    tactics = []

    def show_goal():
        status, detail = run_lean(preamble, sig, tactics)
        if status == "solved":
            print("\n*** NO GOALS REMAIN -- theorem proved! ***")
            print("Proof:\n  {} := by".format(sig))
            for t in tactics:
                print("    " + t)
            return True
        if status == "goals":
            print("\nCurrent goal:\n  " + detail.replace("\n", "\n  "))
        else:
            print("\n[kernel error] " + detail)
        return False

    if show_goal():
        return 0

    while True:
        try:
            line = input("\ntactic> ").strip()
        except EOFError:
            print("\n(end of input)")
            break
        if not line:
            continue
        if line == ":quit":
            break
        if line == ":proof":
            print("  " + ("\n  ".join(tactics) if tactics else "(none yet)"))
            continue
        if line == ":goal":
            show_goal()
            continue
        if line == ":undo":
            if tactics:
                dropped = tactics.pop()
                print("dropped: {}".format(dropped))
            else:
                print("(nothing to undo)")
            show_goal()
            continue
        if line == ":reset":
            tactics = []
            print("(reset)")
            show_goal()
            continue

        # A candidate tactic: try appending it and let the kernel judge.
        trial = tactics + [line]
        status, detail = run_lean(preamble, sig, trial)
        if status == "error":
            # Rejected -- don't keep it.
            print("[rejected] " + detail)
            continue
        # Accepted (solved or made progress).
        tactics = trial
        if status == "solved":
            print("\n*** NO GOALS REMAIN -- theorem proved! ***")
            print("Proof:\n  theorem {} {} := by".format(name, sig))
            for t in tactics:
                print("    " + t)
            break
        print("[accepted]")
        print("Current goal:\n  " + detail.replace("\n", "\n  "))

    return 0


if __name__ == "__main__":
    sys.exit(main())
