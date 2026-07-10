#!/usr/bin/env python3
"""
Agent-Solver Loop: an LLM-guided forward-chaining theorem prover (proof-of-concept).

Three components:
  1. Formal Sandbox   - the "kernel". Trusts nothing; only accepts valid inferences.
  2. Heuristic Agent  - the "intuition". An LLM (Ollama) that guesses which two
                        theorems are worth combining, to avoid combinatorial blowup.
  3. Execution Loop   - drives the agent, checks its guesses against the sandbox,
                        grows the database, and stops when the target is derived.

Standard library only. Run `python3 agent_solver_loop.py --help` for options.
"""

import argparse
import json
import re
import sys
import urllib.request
import urllib.error


# --------------------------------------------------------------------------- #
# 1. THE FORMAL SANDBOX  (the trusted kernel)
# --------------------------------------------------------------------------- #
# The sandbox is deliberately dumb and strict. It has exactly one inference
# rule: hypothetical syllogism (transitivity of implication). The LLM never
# gets to *assert* a theorem -- it can only *propose* a combination, which the
# sandbox either derives correctly or rejects. This is the security boundary
# that makes an unreliable agent safe to use: hallucinations can waste time,
# but they can never introduce a false theorem.

# A single antecedent/consequent, e.g. "A -> B". We keep the atom grammar
# permissive (alphanumerics + underscore) so you can rename to real lemmas later.
IMPL_RE = re.compile(r"^\s*([A-Za-z0-9_]+)\s*->\s*([A-Za-z0-9_]+)\s*$")


def parse_impl(theorem):
    """Parse 'P -> Q' into ('P', 'Q'); return None if it isn't an implication."""
    if not isinstance(theorem, str):
        return None
    m = IMPL_RE.match(theorem)
    if not m:
        return None
    return m.group(1), m.group(2)


def apply_rule(t1, t2):
    """
    The ONLY inference rule. Transitivity / hypothetical syllogism:

        (P -> Q), (Q -> R)  |-  (P -> R)

    Order matters: the consequent of t1 must equal the antecedent of t2.
    Returns the derived theorem string, or None if the combination is invalid.
    """
    left = parse_impl(t1)
    right = parse_impl(t2)
    if left is None or right is None:
        return None
    p, q = left
    q2, r = right
    if q != q2:
        return None
    if p == r:
        # A -> A is a tautology, not a useful new theorem. Reject to keep the
        # database free of trivial cycles.
        return None
    return "{} -> {}".format(p, r)


# --------------------------------------------------------------------------- #
# 2. THE HEURISTIC AGENT  (the intuition engine)
# --------------------------------------------------------------------------- #
# The agent's ONLY job is to pick two IDs from the database. It never decides
# what is true -- it decides what is worth *trying*. This is the whole point of
# the architecture: with N theorems there are N*(N-1) ordered pairs, and real
# libraries have millions of lemmas. The LLM is the pruning heuristic that
# steers the search toward the goal instead of enumerating useless truths.

AGENT_SYSTEM = """You are the intuition engine of an automated theorem prover.
You are given a database of proven theorems (implications of the form "X -> Y")
and a TARGET conjecture we want to derive. The only inference rule available is
transitivity: from (P -> Q) and (Q -> R) you may derive (P -> R).

Your task: choose the TWO theorem IDs whose combination best advances us toward
the target. Prefer combinations that are VALID (consequent of the first equals
antecedent of the second) and that build a chain reaching the target's atoms.

Respond with STRICT JSON and nothing else:
{"id1": "<id>", "id2": "<id>", "reasoning": "<one short sentence>"}"""


def build_user_prompt(db, target, failed_pairs):
    db_lines = "\n".join("  {}: {}".format(tid, formula)
                         for tid, formula in db.items())
    prompt = [
        "THEOREM DATABASE:",
        db_lines,
        "",
        "TARGET CONJECTURE: " + target,
        "",
        "Remember: id1's consequent must match id2's antecedent for the rule to fire.",
    ]
    if failed_pairs:
        recent = ", ".join("({}, {})".format(a, b) for a, b in failed_pairs[-8:])
        prompt.append("")
        prompt.append("These pairs were already tried and did NOT help; pick "
                      "something else: " + recent)
    prompt.append("")
    prompt.append('Return ONLY: {"id1": "...", "id2": "...", "reasoning": "..."}')
    return "\n".join(prompt)


def query_agent(db, target, failed_pairs, model, url, timeout):
    """
    Ask Ollama for two theorem IDs. Returns (id1, id2, reasoning).

    Raises AgentError on any transport / decoding failure so the loop can
    treat "the LLM misbehaved" as a normal, recoverable event.
    """
    payload = {
        "model": model,
        "system": AGENT_SYSTEM,
        "prompt": build_user_prompt(db, target, failed_pairs),
        "stream": False,
        # Ask Ollama to constrain sampling to valid JSON. Not every model honours
        # this perfectly, which is exactly why the loop still validates the result.
        "format": "json",
        # Reasoning models (qwen3, deepseek-r1, ...) otherwise emit their answer
        # into a separate "thinking" channel and leave "response" empty. Ask them
        # to skip it; harmless for models that don't support the flag.
        "think": False,
        "options": {"temperature": 0.3},
    }
    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        url, data=data, headers={"Content-Type": "application/json"}
    )

    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read().decode("utf-8")
    except urllib.error.URLError as e:
        raise AgentError("cannot reach Ollama at {}: {}".format(url, e))
    except Exception as e:  # noqa: BLE001 - transport is genuinely unpredictable
        raise AgentError("HTTP failure: {}".format(e))

    # Ollama wraps the model's text in {"response": "..."}. Reasoning models may
    # instead (or additionally) fill a "thinking" field, so accept either.
    try:
        outer = json.loads(raw)
    except json.JSONDecodeError as e:
        raise AgentError("Ollama returned non-JSON envelope: {}".format(e))
    inner_text = outer.get("response") or outer.get("thinking") or ""

    return _parse_agent_json(inner_text)


def _parse_agent_json(text):
    """Extract {id1, id2, reasoning} from possibly-messy model output."""
    text = (text or "").strip()
    # Be forgiving: some models wrap JSON in prose or code fences. Grab the first
    # {...} block if a straight parse fails.
    try:
        obj = json.loads(text)
    except json.JSONDecodeError:
        match = re.search(r"\{.*\}", text, re.DOTALL)
        if not match:
            raise AgentError("no JSON object found in model output: {!r}".format(text[:200]))
        try:
            obj = json.loads(match.group(0))
        except json.JSONDecodeError as e:
            raise AgentError("model output was not valid JSON: {}".format(e))

    if not isinstance(obj, dict) or "id1" not in obj or "id2" not in obj:
        raise AgentError("JSON missing id1/id2: {!r}".format(obj))
    return str(obj["id1"]), str(obj["id2"]), str(obj.get("reasoning", ""))


class AgentError(Exception):
    """Raised when the agent (LLM/transport) misbehaves. Always recoverable."""


# --------------------------------------------------------------------------- #
# 2c. CLAUDE-IN-THE-LOOP AGENT
# --------------------------------------------------------------------------- #
# Instead of an HTTP call to a local model, the intuition engine here is Claude,
# reasoning in the chat. Each pick is expressed as an (id1, id2, reasoning)
# triple. The sandbox still validates everything, so this is exactly the same
# trust model -- Claude proposes, the kernel disposes.

def make_scripted_agent(picks):
    """
    Build an agent function from a list of (id1, id2, reasoning) triples that
    Claude produced by reading the database and target. Drops into solve()
    unchanged, so the same loop, victory check, and error handling apply.
    """
    queue = list(picks)

    def agent(db, target, failed_pairs):
        if not queue:
            raise AgentError("intuition engine has no further picks")
        return queue.pop(0)

    return agent


# --------------------------------------------------------------------------- #
# 2b. OFFLINE FALLBACK AGENT  (so the PoC is runnable without Ollama)
# --------------------------------------------------------------------------- #
# A deterministic stand-in that mimics a *good* heuristic: it scans for the
# first untried pair that actually combines. Not "intelligent", but it lets you
# exercise the whole loop with `--no-llm`, and it's a useful baseline to measure
# whether the LLM is beating brute force.

def query_agent_offline(db, target, failed_pairs, **_ignored):
    tried = set(failed_pairs)
    ids = list(db.keys())
    for a in ids:
        for b in ids:
            if a == b or (a, b) in tried:
                continue
            if apply_rule(db[a], db[b]) is not None:
                return a, b, "offline: first valid untried pair"
    # Nothing new combines; return any untried pair to let the loop notice.
    for a in ids:
        for b in ids:
            if a != b and (a, b) not in tried:
                return a, b, "offline: no valid pair remains"
    raise AgentError("offline agent exhausted the search space")


# --------------------------------------------------------------------------- #
# 3. THE EXECUTION LOOP
# --------------------------------------------------------------------------- #

def solve(db, target, agent_fn, max_iterations=50, verbose=True):
    """
    Drive the agent against the sandbox until the target is derived or we give up.

    Returns a result dict with the outcome, the final database, and a trace.
    """
    db = dict(db)  # don't mutate the caller's database
    known_formulas = set(db.values())
    failed_pairs = []
    trace = []
    next_id = len(db) + 1

    def log(msg):
        if verbose:
            print(msg)

    # Sanity: is the target already present?
    if target in known_formulas:
        log("Target '{}' is already in the database.".format(target))
        return {"solved": True, "target": target, "db": db, "trace": trace,
                "iterations": 0}

    for step in range(1, max_iterations + 1):
        log("\n--- iteration {} ---".format(step))

        # (a) Ask the agent for two IDs.
        try:
            id1, id2, reasoning = agent_fn(db, target, failed_pairs)
        except AgentError as e:
            log("  [agent error] {}".format(e))
            trace.append({"step": step, "error": str(e)})
            continue  # a bad turn from the LLM is not fatal; try again

        log("  agent picks: {} + {}  ({})".format(id1, id2, reasoning[:80]))

        # (b) Guard against hallucinated IDs BEFORE touching the sandbox.
        if id1 not in db or id2 not in db:
            missing = [i for i in (id1, id2) if i not in db]
            log("  [hallucination] non-existent id(s): {}".format(missing))
            failed_pairs.append((id1, id2))
            trace.append({"step": step, "id1": id1, "id2": id2,
                          "error": "unknown id"})
            continue

        # (c) Hand the proposal to the sandbox. This is the only place a theorem
        #     can enter the database, and only if the kernel agrees.
        derived = apply_rule(db[id1], db[id2])
        if derived is None:
            log("  [rejected] {!r} and {!r} do not combine by transitivity."
                .format(db[id1], db[id2]))
            failed_pairs.append((id1, id2))
            trace.append({"step": step, "id1": id1, "id2": id2,
                          "error": "invalid combination"})
            continue

        # (d) Valid inference. Skip if we already knew it (avoid redundant growth).
        if derived in known_formulas:
            log("  [redundant] already knew {!r}.".format(derived))
            failed_pairs.append((id1, id2))
            trace.append({"step": step, "id1": id1, "id2": id2,
                          "derived": derived, "note": "redundant"})
            continue

        new_id = "T{}".format(next_id)
        next_id += 1
        db[new_id] = derived
        known_formulas.add(derived)
        failed_pairs = []  # progress made; forget the dead-ends
        log("  [proved] {} = {!r}   (from {} , {})".format(
            new_id, derived, id1, id2))
        trace.append({"step": step, "id1": id1, "id2": id2,
                      "derived": derived, "new_id": new_id})

        # (e) Victory check.
        if derived == target:
            log("\n*** VICTORY: derived target {!r} as {} ***".format(target, new_id))
            return {"solved": True, "target": target, "db": db,
                    "trace": trace, "iterations": step}

    log("\nGave up after {} iterations without deriving {!r}."
        .format(max_iterations, target))
    return {"solved": False, "target": target, "db": db, "trace": trace,
            "iterations": max_iterations}


# --------------------------------------------------------------------------- #
# Entry point
# --------------------------------------------------------------------------- #

DEFAULT_DB = {
    "T1": "A -> B",
    "T2": "B -> C",
    "T3": "C -> D",
    # A couple of distractors so the agent has to actually choose:
    "T4": "X -> Y",
    "T5": "D -> E",
}
DEFAULT_TARGET = "A -> D"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--target", default=DEFAULT_TARGET,
                    help="conjecture to derive (default: %(default)s)")
    ap.add_argument("--model", default="llama3",
                    help="Ollama model name (default: %(default)s)")
    ap.add_argument("--url", default="http://localhost:11434/api/generate",
                    help="Ollama generate endpoint")
    ap.add_argument("--max-iterations", type=int, default=50)
    ap.add_argument("--timeout", type=float, default=60.0,
                    help="per-request timeout in seconds")
    ap.add_argument("--no-llm", action="store_true",
                    help="use the deterministic offline agent instead of Ollama")
    args = ap.parse_args(argv)

    if args.no_llm:
        agent_fn = query_agent_offline
        print("Using OFFLINE deterministic agent (no Ollama).")
    else:
        def agent_fn(db, target, failed_pairs):
            return query_agent(db, target, failed_pairs, model=args.model,
                               url=args.url, timeout=args.timeout)
        print("Using Ollama model {!r} at {}".format(args.model, args.url))

    print("Database:")
    for tid, formula in DEFAULT_DB.items():
        print("  {}: {}".format(tid, formula))
    print("Target: {}".format(args.target))

    result = solve(DEFAULT_DB, args.target, agent_fn,
                   max_iterations=args.max_iterations)

    print("\n=== final database ===")
    for tid, formula in result["db"].items():
        print("  {}: {}".format(tid, formula))
    return 0 if result["solved"] else 1


if __name__ == "__main__":
    sys.exit(main())
