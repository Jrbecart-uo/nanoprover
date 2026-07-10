"""
The kernel boundary: a uniform interface over a real proof assistant.

`ProofEnv` is the contract the search loop programs against. `apply()` takes a
proof state and a candidate tactic string, hands it to the *real* Lean kernel,
and reports back one of three outcomes -- SOLVED, a new PROGRESS state, or
FAILED. Nothing else in the system is trusted to decide what is provable; this
is the analogue of `apply_rule` from the propositional PoC, except the checking
is done by Lean/mathlib instead of ten lines of Python.

Two implementations:
  * LeanDojoEnv  -- drives Lean 4 + mathlib via LeanDojo. This is the target.
  * MockEnv      -- a toy string-rewrite goal, so the search loop can be
                    exercised end-to-end without a Lean toolchain installed.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Optional


# --------------------------------------------------------------------------- #
# Result types  (what the kernel says back)
# --------------------------------------------------------------------------- #

@dataclass(frozen=True)
class Solved:
    """The tactic closed the goal. The proof is complete along this path."""


@dataclass(frozen=True)
class Progress:
    """The tactic was accepted and produced a new (non-final) goal state."""
    state: "ProofState"


@dataclass(frozen=True)
class Failed:
    """The tactic was rejected by the kernel (type error, no-op, timeout, ...)."""
    message: str


StepResult = object  # one of Solved | Progress | Failed


@dataclass(frozen=True)
class ProofState:
    """
    An opaque handle to a Lean proof state plus its human-readable goal text.

    `key` is used for de-duplication in the search (two paths reaching the same
    goal are the same node). `pp` is the pretty-printed goal the agent reads.
    `handle` carries the backend-specific object (a LeanDojo TacticState) so the
    env can resume from it; the search loop never inspects it.
    """
    key: str
    pp: str
    handle: object = None


# --------------------------------------------------------------------------- #
# Interface
# --------------------------------------------------------------------------- #

class ProofEnv(ABC):
    @abstractmethod
    def initial_state(self) -> ProofState:
        ...

    @abstractmethod
    def apply(self, state: ProofState, tactic: str) -> StepResult:
        """Run one tactic against the kernel. Returns Solved | Progress | Failed."""

    def close(self) -> None:  # optional cleanup hook
        pass

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()


# --------------------------------------------------------------------------- #
# LeanDojo-backed environment  (the real kernel)
# --------------------------------------------------------------------------- #

class LeanDojoEnv(ProofEnv):
    """
    Wraps a single theorem in a Lean repo as an interactive proving session.

    NOTE ON VERSION DRIFT: LeanDojo's result classes and method names have moved
    between releases. This targets the common surface (`Dojo`, `run_tac`,
    `TacticState`, `ProofFinished`, `LeanError`). If your installed version
    differs, the failure will be a clean ImportError / AttributeError here --
    adjust the imports below to match `python -c "import lean_dojo; help(lean_dojo)"`.

    Setup is in README.md; this class assumes `pip install lean-dojo` succeeded
    and the repo has been traced once.
    """

    def __init__(self, repo_url: str, commit: str, file_path: str, theorem_fqn: str):
        # Imported lazily so the rest of the package (and MockEnv) works with no
        # Lean toolchain present.
        from lean_dojo import LeanGitRepo, Theorem, Dojo  # type: ignore

        self._repo = LeanGitRepo(repo_url, commit)
        self._theorem = Theorem(self._repo, file_path, theorem_fqn)
        self._dojo_cm = Dojo(self._theorem)
        self._dojo, init = self._dojo_cm.__enter__()
        self._init = self._wrap(init)

    def _wrap(self, tactic_state) -> ProofState:
        # `.pp` is the pretty-printed goal; `.id` uniquely identifies the state.
        pp = getattr(tactic_state, "pp", str(tactic_state))
        key = str(getattr(tactic_state, "id", pp))
        return ProofState(key=key, pp=pp, handle=tactic_state)

    def initial_state(self) -> ProofState:
        return self._init

    def apply(self, state: ProofState, tactic: str) -> StepResult:
        from lean_dojo import ProofFinished, LeanError  # type: ignore
        try:
            result = self._dojo.run_tac(state.handle, tactic)
        except Exception as e:  # transport / process death
            return Failed("dojo.run_tac raised: {}".format(e))

        if isinstance(result, ProofFinished):
            return Solved()
        if isinstance(result, LeanError):
            return Failed(getattr(result, "message", "LeanError"))
        # Anything else that carries a goal is a new TacticState (or a timeout /
        # given-up wrapper). Treat a missing `.pp` as failure to be safe.
        if hasattr(result, "pp") or hasattr(result, "id"):
            return Progress(self._wrap(result))
        return Failed("non-progress result: {!r}".format(type(result).__name__))

    def close(self) -> None:
        try:
            self._dojo_cm.__exit__(None, None, None)
        except Exception:
            pass


# --------------------------------------------------------------------------- #
# Mock environment  (offline; lets you run the whole loop with no Lean)
# --------------------------------------------------------------------------- #

class MockEnv(ProofEnv):
    """
    A stand-in "kernel" over a trivial rewrite calculus, purely to exercise the
    search + agent plumbing without Lean. The goal is a string; a tactic named
    `rw <a>-><b>` rewrites the first `a` into `b`. The goal is SOLVED when it
    equals the target string. Unknown/again-inapplicable tactics FAIL.

    This mirrors the shape of a real backward proof: each step transforms the
    goal, and only the kernel (here, this class) decides if a step is legal.
    """

    def __init__(self, start: str = "a + b + c", target: str = "SUM"):
        self._start = start
        self._target = target
        # A tiny, fixed rewrite table. The agent doesn't get to invent these --
        # it can only propose applying them, and MockEnv validates.
        self._rules = {
            "a + b": "S1",
            "S1 + c": "S2",
            "S2": "SUM",
            "b + c": "S3",  # a decoy path that dead-ends
        }

    def rules(self):
        return dict(self._rules)

    def initial_state(self) -> ProofState:
        return ProofState(key=self._start, pp=self._start, handle=self._start)

    def apply(self, state: ProofState, tactic: str) -> StepResult:
        goal = state.handle
        if not tactic.startswith("rw "):
            return Failed("mock only understands 'rw <lhs>-><rhs>'")
        try:
            lhs, rhs = tactic[3:].split("->", 1)
            lhs, rhs = lhs.strip(), rhs.strip()
        except ValueError:
            return Failed("malformed rewrite: {!r}".format(tactic))
        if self._rules.get(lhs) != rhs:
            return Failed("no such rewrite rule: {} -> {}".format(lhs, rhs))
        if lhs not in goal:
            return Failed("lhs {!r} does not occur in goal {!r}".format(lhs, goal))
        new_goal = goal.replace(lhs, rhs, 1)
        if new_goal == self._target:
            return Solved()
        return Progress(ProofState(key=new_goal, pp=new_goal, handle=new_goal))
