"""
A lightweight real-Lean kernel, without the full LeanDojo trace.

LeanDojoEnv (in proof_env.py) gives you interactive, subgoal-level proof states
but requires tracing the whole repo + dependencies first -- minutes to hours.
When the theorem's context has no heavy dependencies (only Lean core, or a
small library), you don't need that: you can hand a candidate proof straight to
the `lean` binary and ask the kernel to typecheck it.

LeanCLIEnv implements the same ProofEnv contract by writing a probe file
    <preamble>
    theorem <name> <signature> := by
      <tactic>
and running `lean` on it. Exit 0 => the kernel accepts the proof (SOLVED).
Non-zero => rejected (FAILED). This is "whole-proof" checking rather than
incremental state, so it can't expose subgoals -- but it is a genuine kernel
check, and it runs in well under a second per candidate.

This is the env used for the real end-to-end demo, because a full LeanDojo
trace does not fit a 10-minute-per-step budget.
"""

from __future__ import annotations

import os
import subprocess
import tempfile

from proof_env import ProofEnv, ProofState, Solved, Progress, Failed


class LeanCLIEnv(ProofEnv):
    def __init__(self, signature: str, preamble: str = "",
                 lean_cmd=None, cwd: str | None = None,
                 timeout: float = 60.0):
        """
        signature: the theorem binders + goal, e.g.
                   "(a b c : Nat) : a + b + c = a + c + b"
        preamble:  lines that must precede the theorem (imports, `open ...`).
        lean_cmd:  command list, default ["lean"]. Use ["lake", "env", "lean"]
                   with cwd=<mathlib checkout> to resolve `import Mathlib.*`
                   against the prebuilt cache (`lake exe cache get`).
        cwd:       run from here so elan resolves the right toolchain
                   (a directory containing a `lean-toolchain` file).
        """
        self._sig = signature.strip()
        self._preamble = preamble
        self._lean_cmd = list(lean_cmd) if lean_cmd else ["lean"]
        self._cwd = cwd
        self._timeout = timeout

    def initial_state(self) -> ProofState:
        # The "state" is just the goal text; there is no interactive handle.
        return ProofState(key=self._sig, pp=self._sig, handle=self._sig)

    def apply(self, state: ProofState, tactic: str):
        # Build a probe file: the theorem closed by this single tactic.
        body = "{}\ntheorem __probe__ {} := by\n  {}\n".format(
            self._preamble, self._sig, tactic)
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
            f.write(body)
            path = f.name
        try:
            proc = subprocess.run(
                self._lean_cmd + [path],
                cwd=self._cwd, capture_output=True, text=True,
                timeout=self._timeout,
            )
        except subprocess.TimeoutExpired:
            return Failed("lean timed out on tactic {!r}".format(tactic))
        finally:
            try:
                os.unlink(path)
            except OSError:
                pass

        if proc.returncode == 0 and not proc.stderr.strip():
            # Kernel accepted the whole proof.
            return Solved()
        # Rejected: surface the first error line for the log.
        msg = (proc.stdout + proc.stderr).strip().splitlines()
        first = next((l for l in msg if "error" in l.lower()), msg[0] if msg else "rejected")
        return Failed(first[:200])
