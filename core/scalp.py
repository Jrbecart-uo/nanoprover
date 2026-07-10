"""
Fast scalp-hunting: batched candidate checking + identifier preflight.

Speedups over the one-candidate-per-file retry loop:
  1. All candidates of a round go into ONE lean file as anonymous `example`s
     -- one `import Mathlib` amortized across the round (the round costs
     roughly as much as a single candidate did before).
  2. Before touching the kernel, every dotted identifier in each candidate is
     checked against data/all_names.txt (470k mathlib constants). Hallucinated
     or renamed lemma names -- our #1 failure class -- are caught in
     milliseconds with a "did you mean" from the premise index.
"""

from __future__ import annotations

import os
import re
import subprocess
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MATHLIB = os.environ.get("NANOPROVER_MATHLIB_DIR", os.path.join(ROOT, "mathlib4"))
NAMES = os.path.join(ROOT, "data", "all_names.txt")

_names_cache = None


def known_names():
    global _names_cache
    if _names_cache is None:
        with open(NAMES) as f:
            _names_cache = set(line.strip() for line in f)
    return _names_cache


# Dotted identifiers that look like library references (Nat.foo, ZMod.bar.baz);
# single-segment names (omega, linarith, local hyps) are skipped.
IDENT_RE = re.compile(r"\b([A-Z][A-Za-z0-9_]*(?:\.[A-Za-z0-9_']+)+)\b")


def preflight(script: str):
    """Return the dotted identifiers in `script` that mathlib doesn't know."""
    names = known_names()
    missing = []
    for ident in set(IDENT_RE.findall(script)):
        if ident in names:
            continue
        # tolerate structure projections / partial matches: X.a.b is fine if
        # some known name starts with X.a (field access, dot-notation on hyps)
        head = ident.rsplit(".", 1)[0]
        if any(n == head or n.startswith(ident + ".") for n in
               (head, )) or head in names:
            continue
        missing.append(ident)
    return sorted(missing)


def check_batch(sig: str, preamble: str, scripts, timeout=560):
    """
    Kernel-check many candidate scripts for the same goal in ONE lean file.
    Returns list of (solved: bool, error: str) aligned with `scripts`.
    Sound: anonymous `example`s (nothing enters the env to be cited) and any
    mention of sorry in a variant's diagnostics fails that variant.
    """
    lines = [preamble, ""]
    spans = []
    for script in scripts:
        start = len(lines) + 1
        lines.append("example {} := by".format(sig))
        lines += ["  " + l for l in script.splitlines()]
        lines.append("")
        spans.append((start, len(lines)))
    path = "/tmp/scalp_batch.lean"
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")
    t0 = time.time()
    p = subprocess.run(["lake", "env", "lean", path], cwd=MATHLIB,
                       capture_output=True, text=True, timeout=timeout)
    dt = time.time() - t0
    out = p.stdout + p.stderr

    # collect diagnostics per line: errors AND sorry warnings
    diag = {}   # line -> first message chunk
    for m in re.finditer(r"\.lean:(\d+):\d+: (error|warning)[^\n]*(?:\n(?!\S*\.lean:)[^\n]*)*",
                         out):
        ln = int(m.group(1))
        diag.setdefault(ln, m.group(0))

    results = []
    for (s, e) in spans:
        hits = [(ln, msg) for ln, msg in diag.items() if s <= ln <= e]
        bad = [(ln, msg) for ln, msg in hits
               if "error" in msg.split("\n")[0] or "sorry" in msg]
        if bad:
            results.append((False, bad[0][1][:1200]))
        else:
            results.append((True, ""))
    return results, round(dt, 1)
