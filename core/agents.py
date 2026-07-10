"""
The intuition layer: tactic generators.

Each agent looks at a goal state and proposes candidate tactics (with a rough
score). None of them decide truth -- the kernel (proof_env) does. The
PortfolioAgent is the "combine them all" idea done correctly: it merges
proposals from several sources at the *tactic* level, so cheap deterministic
tactics, an LLM, and (optionally) a Lean-native prover model all compete on the
same goal and the kernel keeps whatever closes it.

  * BuiltinAgent    -- zero-cost, always-worth-trying Lean tactics (simp, aesop...)
  * ClaudeAgent     -- Claude via the Anthropic SDK, structured JSON output
  * DeepSeekAgent   -- an OpenAI-compatible local endpoint (vLLM/Ollama) for a
                       Lean-native open model; stubbed, wire up to taste
  * PortfolioAgent  -- fans out to a list of the above and dedupes
"""

from __future__ import annotations

import json
import os
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import List


@dataclass(frozen=True)
class Candidate:
    tactic: str
    score: float          # higher = try first
    source: str           # which agent proposed it (for logging)


class TacticAgent(ABC):
    name = "agent"

    @abstractmethod
    def propose(self, goal_pp: str, k: int) -> List[Candidate]:
        """Return up to k candidate tactics for the given goal text."""


# --------------------------------------------------------------------------- #
# Cheap deterministic baseline
# --------------------------------------------------------------------------- #

class MockRewriteAgent(TacticAgent):
    """
    A deterministic intuition engine for MockEnv only: proposes `rw a->b` for
    each known rewrite rule. Lets the offline demo reach a real solution without
    any LLM, so you can watch best-first search work (including avoiding the
    dead-end decoy). This is the Lean-skeleton analogue of the scripted agent
    from the propositional PoC.
    """
    name = "mock-oracle"

    def __init__(self, rules: dict):
        self._rules = dict(rules)

    def propose(self, goal_pp: str, k: int) -> List[Candidate]:
        out = []
        for lhs, rhs in self._rules.items():
            # Only propose rewrites that actually apply to this goal, and score
            # a rule that moves toward the target ('SUM') higher.
            if lhs in goal_pp:
                score = 2.0 if rhs == "SUM" else 1.0
                out.append(Candidate("rw {}->{}".format(lhs, rhs),
                                     score=score, source=self.name))
        return out[:k]


class BuiltinAgent(TacticAgent):
    """
    The "free" tactics. In real Lean these close a surprising fraction of goals
    on their own, so they belong at the front of every portfolio -- they cost no
    tokens and no model latency. Score them high so the search tries them first.
    """
    name = "builtin"

    DEFAULT_TACTICS = [
        "rfl", "simp", "aesop", "omega", "norm_num", "linarith",
        "exact?", "decide", "tauto", "ring",
    ]

    def __init__(self, tactics=None):
        self._tactics = list(tactics or self.DEFAULT_TACTICS)

    def propose(self, goal_pp: str, k: int) -> List[Candidate]:
        return [Candidate(t, score=1.0, source=self.name)
                for t in self._tactics[:k]]


# --------------------------------------------------------------------------- #
# Claude as the intuition engine
# --------------------------------------------------------------------------- #

CLAUDE_SYSTEM = """You are the intuition engine of a Lean 4 / mathlib theorem prover.
You are shown the current proof goal (Lean tactic-state pretty-print). Propose
the tactics most likely to make progress or close the goal.

Prefer tactics that are valid Lean 4 mathlib syntax. Order them best-first.
Favor a mix: a direct closer (e.g. `simp`, `aesop`, `exact ...`) and one or two
structural moves (`intro`, `rcases`, `induction`, `rw [...]`, `apply ...`).
Return ONLY the structured JSON requested; no prose."""

# Structured-output schema: guarantees we get back parseable JSON, so the search
# loop never has to defensively parse model prose.
TACTIC_SCHEMA = {
    "type": "object",
    "properties": {
        "tactics": {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    "tactic": {"type": "string"},
                    "confidence": {"type": "number"},
                    "reason": {"type": "string"},
                },
                "required": ["tactic", "confidence", "reason"],
                "additionalProperties": False,
            },
        }
    },
    "required": ["tactics"],
    "additionalProperties": False,
}


class ClaudeAgent(TacticAgent):
    """
    Calls Claude through the official Anthropic SDK. Auth resolves from the
    environment (ANTHROPIC_API_KEY or an `ant auth login` profile) -- no key is
    hardcoded. Uses structured outputs so the response is schema-valid JSON.
    """
    name = "claude"

    def __init__(self, model: str = "claude-opus-4-8", max_candidates: int = 6,
                 effort: str = "high"):
        # Imported lazily so the package loads without `anthropic` installed
        # (e.g. when only running the MockEnv + BuiltinAgent offline).
        import anthropic  # type: ignore
        self._client = anthropic.Anthropic()
        self._model = model
        self._max = max_candidates
        self._effort = effort

    def propose(self, goal_pp: str, k: int) -> List[Candidate]:
        user = (
            "Current Lean proof goal:\n\n```\n{}\n```\n\n"
            "Propose up to {} tactics, best first."
        ).format(goal_pp, min(k, self._max))

        # Fable 5 / Opus 4.8: no temperature/top_p (they 400); adaptive thinking
        # is optional. Effort controls depth. Structured output forces valid JSON.
        resp = self._client.messages.create(
            model=self._model,
            max_tokens=2048,
            system=CLAUDE_SYSTEM,
            output_config={
                "effort": self._effort,
                "format": {"type": "json_schema", "schema": TACTIC_SCHEMA},
            },
            messages=[{"role": "user", "content": user}],
        )
        text = next((b.text for b in resp.content if b.type == "text"), "")
        try:
            data = json.loads(text)
        except json.JSONDecodeError:
            return []  # a bad turn is recoverable; the loop just tries again
        out = []
        for item in data.get("tactics", [])[:k]:
            tac = str(item.get("tactic", "")).strip()
            if not tac:
                continue
            conf = float(item.get("confidence", 0.5))
            out.append(Candidate(tac, score=conf, source=self.name))
        return out


# --------------------------------------------------------------------------- #
# A Lean-native open model (DeepSeek-Prover, via an OpenAI-compatible endpoint)
# --------------------------------------------------------------------------- #

class DeepSeekProverAgent(TacticAgent):
    """
    Stub for a locally-served Lean-native prover (DeepSeek-Prover on vLLM, or an
    Ollama model). Kept in the portfolio as an open-weight second opinion to
    benchmark against Claude. Fill in `propose()` with your endpoint's protocol;
    the important thing is it returns Candidate objects like everyone else.
    """
    name = "deepseek-prover"

    def __init__(self, base_url: str = "http://localhost:8000/v1",
                 model: str = "deepseek-prover-v2"):
        self._base_url = base_url
        self._model = model

    def propose(self, goal_pp: str, k: int) -> List[Candidate]:
        # TODO: POST to {base_url}/completions with a Lean-proof prompt, parse
        # the emitted tactic(s). Returning [] means "this source had nothing",
        # which the portfolio handles gracefully.
        return []


# --------------------------------------------------------------------------- #
# The portfolio -- "combine them all", correctly, at the tactic level
# --------------------------------------------------------------------------- #

class PortfolioAgent(TacticAgent):
    name = "portfolio"

    def __init__(self, agents: List[TacticAgent]):
        self._agents = list(agents)

    def propose(self, goal_pp: str, k: int) -> List[Candidate]:
        merged = {}
        for agent in self._agents:
            try:
                cands = agent.propose(goal_pp, k)
            except Exception as e:
                # One misbehaving source (network blip, model error) must not
                # sink the whole expansion. Log-and-continue.
                print("  [portfolio] {} failed: {}".format(agent.name, e))
                cands = []
            for c in cands:
                # Dedupe by tactic string; keep the highest-scoring proposer.
                prev = merged.get(c.tactic)
                if prev is None or c.score > prev.score:
                    merged[c.tactic] = c
        ranked = sorted(merged.values(), key=lambda c: c.score, reverse=True)
        return ranked[:k]


# --------------------------------------------------------------------------- #
# Retrieval-augmented proposer -- premise selection from the local index
# --------------------------------------------------------------------------- #

class LibraryAgent(TacticAgent):
    """
    Proposes tactics built from mathlib lemmas retrieved from the local
    premise index (tools/premise_index.py). No LLM involved: retrieval is
    BM25 over lemma names + statements, and the kernel filters everything.
    For each of the top-k retrieved lemmas L we propose the standard usage
    forms; wrong guesses are just rejected steps.
    """
    name = "library"

    def __init__(self, k: int = 5):
        import os, sys
        tools = os.path.join(os.path.dirname(os.path.dirname(
            os.path.abspath(__file__))), "tools")
        if tools not in sys.path:
            sys.path.insert(0, tools)
        import premise_index
        self._pi = premise_index
        self._k = k

    def propose(self, goal_pp: str, k: int) -> List[Candidate]:
        terms = self._pi.goal_terms(goal_pp)
        if not terms:
            return []
        out = []
        for rank, (name, stmt, _score) in enumerate(self._pi.query(terms, self._k)):
            base = 0.9 - 0.1 * rank        # rank 0 -> 0.9, rank 4 -> 0.5
            out.append(Candidate("exact {}".format(name), base, self.name))
            out.append(Candidate("apply {}".format(name), base - 0.03, self.name))
            out.append(Candidate("simp [{}]".format(name), base - 0.06, self.name))
        return out[:k]
