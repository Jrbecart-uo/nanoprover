"""
Error-feedback retry: the proposal channel, closed into a loop.

Lesson learned on miniF2F's mathd_numbertheory_353: proposing blind fails on
hallucinated lemma names, and the proposer never saw the kernel's error text
("unknown constant ...", "motive is not type correct", ...). This module feeds
each failure back to the proposer so the next attempt is informed.

    result = propose_with_feedback(env, proposer, max_rounds=4)

`proposer(goal_pp, history)` returns the next candidate script, where history
is a list of (script, error) pairs from prior rounds. Three implementations:

  * ClaudeRetryProposer  -- Anthropic API; premises + full failure history in
                            the prompt (needs ANTHROPIC_API_KEY).
  * InteractiveProposer  -- a human (or session LLM) at the terminal: sees the
                            error, types the next script; multi-line, end with
                            a lone '.'
  * ScriptedProposer     -- fixed list of attempts (for tests/replays).
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Callable, List, Optional, Tuple

from proof_env import ProofEnv, Solved, Failed


@dataclass
class RetryResult:
    solved: bool
    script: Optional[str]
    rounds: int
    history: List[Tuple[str, str]] = field(default_factory=list)


def propose_with_feedback(env: ProofEnv, proposer: Callable,
                          max_rounds: int = 4, verbose: bool = True) -> RetryResult:
    """Run proposer -> kernel -> error feedback -> proposer, up to max_rounds."""
    state = env.initial_state()
    history: List[Tuple[str, str]] = []
    for rnd in range(1, max_rounds + 1):
        script = proposer(state.pp, history)
        if script is None:
            break
        result = env.apply(state, script)
        if isinstance(result, Solved):
            if verbose:
                print("[round {}] ACCEPTED by kernel".format(rnd))
            return RetryResult(True, script, rnd, history)
        error = result.message if isinstance(result, Failed) else "made progress but did not close"
        history.append((script, error))
        if verbose:
            print("[round {}] rejected: {}".format(rnd, error[:160]))
    return RetryResult(False, None, len(history), history)


# --------------------------------------------------------------------------- #
# Proposers
# --------------------------------------------------------------------------- #

class ScriptedProposer:
    """Replay a fixed attempt list (testing / offline replays)."""

    def __init__(self, scripts: List[str]):
        self._scripts = list(scripts)

    def __call__(self, goal_pp, history):
        i = len(history)
        return self._scripts[i] if i < len(self._scripts) else None


class InteractiveProposer:
    """Human / session-LLM at a terminal. Multi-line script; end with '.'"""

    def __call__(self, goal_pp, history):
        if not history:
            print("GOAL:\n  " + goal_pp)
        else:
            print("LAST ERROR:\n  " + history[-1][1])
        print("enter script (end with '.' on its own line, or ':quit'):")
        lines = []
        while True:
            try:
                line = input()
            except EOFError:
                return None
            if line.strip() == ":quit":
                return None
            if line.strip() == ".":
                break
            lines.append(line)
        return "\n".join(lines) if lines else None


RETRY_SYSTEM = """You are the intuition engine of a Lean 4 / mathlib theorem prover,
in an error-feedback loop. You will see the goal, retrieved premises, and the
FULL HISTORY of your failed attempts with the kernel's exact error for each.
Diagnose the error (unknown constant means the lemma name does not exist --
prefer names appearing in the retrieved premises; type mismatches usually mean
a cast or an argument-order fix) and produce ONE revised complete tactic
script. Return strictly {"script": "..."} as JSON; no prose."""


class ClaudeRetryProposer:
    """Anthropic-API proposer with premises + failure history in the prompt."""

    def __init__(self, model: str = "claude-opus-4-8", premise_k: int = 10):
        import anthropic  # lazy: keyless installs still import this module
        self._client = anthropic.Anthropic()
        self._model = model
        self._pi = None
        self._premise_k = premise_k
        try:
            import os, sys
            tools = os.path.join(os.path.dirname(os.path.dirname(
                os.path.abspath(__file__))), "tools")
            sys.path.insert(0, tools)
            import premise_index
            self._pi = premise_index
        except Exception:
            pass

    def __call__(self, goal_pp, history):
        premises = "(no index)"
        if self._pi:
            try:
                rows = self._pi.query(self._pi.goal_terms(goal_pp), self._premise_k)
                premises = "\n".join("- {} : {}".format(n, t) for n, t, _ in rows)
            except Exception:
                pass
        hist = "\n\n".join(
            "ATTEMPT {}:\n{}\nKERNEL ERROR:\n{}".format(i + 1, s, e)
            for i, (s, e) in enumerate(history)) or "(first attempt)"
        user = ("GOAL:\n```\n{}\n```\n\nRETRIEVED PREMISES:\n{}\n\n"
                "HISTORY:\n{}\n\nProduce the next script.").format(
                    goal_pp, premises, hist)
        resp = self._client.messages.create(
            model=self._model, max_tokens=2048, system=RETRY_SYSTEM,
            output_config={"effort": "high", "format": {"type": "json_schema",
                "schema": {"type": "object",
                           "properties": {"script": {"type": "string"}},
                           "required": ["script"],
                           "additionalProperties": False}}},
            messages=[{"role": "user", "content": user}])
        text = next((b.text for b in resp.content if b.type == "text"), "{}")
        try:
            return json.loads(text).get("script")
        except json.JSONDecodeError:
            return None
