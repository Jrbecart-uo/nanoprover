"""
Best-first backward search over proof states.

This is the "execution loop" of the Lean version, and the key upgrade over the
propositional PoC: it searches *backward* from the goal. Each node is a proof
state; expanding a node means asking the portfolio agent for candidate tactics
and running each against the kernel. Tactics that close the goal win; tactics
that make progress push new nodes; tactics the kernel rejects are dropped.

A priority queue ordered by a heuristic (here: agent score + depth penalty)
gives best-first behaviour -- the frontier explores the most promising states
first instead of blindly enumerating, which is the whole reason to have an
LLM in the loop.
"""

from __future__ import annotations

import heapq
import itertools
from dataclasses import dataclass, field
from typing import List, Optional

from proof_env import ProofEnv, ProofState, Solved, Progress, Failed
from agents import TacticAgent, Candidate


@dataclass
class Node:
    state: ProofState
    path: List[str]           # tactics applied from the root to reach this state
    priority: float           # lower = explored sooner (heapq is a min-heap)


@dataclass
class SearchResult:
    solved: bool
    proof: Optional[List[str]]     # the winning tactic sequence, if solved
    expansions: int                # how many states we expanded
    tactics_tried: int             # how many kernel calls we made


def search(env: ProofEnv, agent: TacticAgent,
           branching: int = 8, max_expansions: int = 200,
           verbose: bool = True) -> SearchResult:
    """
    Drive `agent` (proposer) against `env` (kernel) until the goal is proved
    or the expansion budget runs out.
    """
    def log(msg):
        if verbose:
            print(msg)

    root = env.initial_state()
    counter = itertools.count()          # tie-breaker so heapq never compares Nodes
    frontier: list = []
    heapq.heappush(frontier, (0.0, next(counter), Node(root, [], 0.0)))
    seen = {root.key}
    expansions = 0
    tactics_tried = 0

    while frontier and expansions < max_expansions:
        _, _, node = heapq.heappop(frontier)
        expansions += 1
        log("\n[expand #{}] depth {}  goal: {}".format(
            expansions, len(node.path), _oneline(node.state.pp)))

        candidates = agent.propose(node.state.pp, branching)
        if not candidates:
            log("  (no candidates proposed)")
            continue

        for cand in candidates:
            tactics_tried += 1
            result = env.apply(node.state, cand.tactic)

            if isinstance(result, Solved):
                proof = node.path + [cand.tactic]
                log("  [SOLVED] via {!r}  ({})".format(cand.tactic, cand.source))
                log("\n*** PROOF FOUND ({} tactics) ***".format(len(proof)))
                for i, t in enumerate(proof, 1):
                    log("  {}. {}".format(i, t))
                return SearchResult(True, proof, expansions, tactics_tried)

            if isinstance(result, Failed):
                log("  [reject] {!r} -> {}".format(cand.tactic, _oneline(result.message)))
                continue

            # Progress: a new goal state.
            assert isinstance(result, Progress)
            child = result.state
            if child.key in seen:
                log("  [dup] {!r} -> already-seen state".format(cand.tactic))
                continue
            seen.add(child.key)

            # Priority: prefer high agent score, penalise depth so the search
            # doesn't chase one long branch forever. Lower = sooner.
            depth = len(node.path) + 1
            priority = depth - cand.score
            heapq.heappush(frontier, (priority, next(counter),
                                      Node(child, node.path + [cand.tactic], priority)))
            log("  [push] {!r} -> {}  (prio {:.2f})".format(
                cand.tactic, _oneline(child.pp), priority))

    log("\nExhausted budget: {} expansions, {} tactic attempts, no proof."
        .format(expansions, tactics_tried))
    return SearchResult(False, None, expansions, tactics_tried)


def _oneline(s: str, width: int = 70) -> str:
    s = " ".join(str(s).split())
    return s if len(s) <= width else s[:width - 1] + "…"
