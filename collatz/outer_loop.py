"""
OUTER LOOP, step 3: the kernel filters the proposed gear.

For each candidate lemma, try its proof attempts in order against the real Lean
kernel. Outcomes:
  PROVED    -- joins the rule set (and becomes available to later candidates)
  REJECTED  -- every attempt failed with a hard error
  (A candidate that is true-but-unproven and one that is false land in the same
   bucket from the kernel's point of view: no accepted proof, no entry. Honest.)
"""

import os
import subprocess
import tempfile

from gear_candidates import PRELUDE, EXISTING_GEAR, CANDIDATES

REPO = os.environ.get("NANOPROVER_LEAN_DIR",
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lean4-example"))


def lean_check(source: str, timeout=60):
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(source)
        path = f.name
    try:
        p = subprocess.run(["lean", path], cwd=REPO, capture_output=True,
                           text=True, timeout=timeout)
        out = (p.stdout + p.stderr).strip()
        ok = p.returncode == 0 and "sorry" not in out.lower() and "error" not in out.lower()
        return ok, out
    finally:
        os.unlink(path)


def main():
    proved_gear = []          # accumulated source of accepted lemmas
    results = []
    for cand in CANDIDATES:
        accepted = None
        last_err = ""
        for i, attempt in enumerate(cand["attempts"], 1):
            src = (PRELUDE + EXISTING_GEAR + "\n".join(proved_gear) + "\n"
                   + cand["statement"] + " " + attempt + "\n")
            ok, out = lean_check(src)
            if ok:
                accepted = (i, cand["statement"] + " " + attempt)
                break
            last_err = out.splitlines()[0] if out else "(no output)"
        if accepted:
            proved_gear.append(accepted[1])
            results.append((cand["name"], "PROVED (attempt {})".format(accepted[0])))
        else:
            results.append((cand["name"], "REJECTED [{}]".format(last_err[:90])))

    print("=" * 74)
    print("OUTER LOOP RESULTS -- kernel-filtered gear")
    print("=" * 74)
    for name, verdict in results:
        print("  {:22s} {}".format(name, verdict))
    print()
    print("{} of {} candidates survived the kernel.".format(
        len(proved_gear), len(CANDIDATES)))

    # Persist the surviving gear for the regenerated discovery loop.
    with open(os.path.join(os.path.dirname(__file__), "proved_gear.lean"), "w") as f:
        f.write(PRELUDE + EXISTING_GEAR + "\n".join(proved_gear) + "\n")
    print("surviving gear written to lean_solver/proved_gear.lean")


if __name__ == "__main__":
    main()
