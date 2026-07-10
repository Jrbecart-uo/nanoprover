"""
Local premise-selection index over the mathlib theorem database.

Why an index: `exact?` re-scans Lean's whole environment on every call (fine
interactively, slow and opaque in a pipeline), and a 319k-line TSV has no
ranking. SQLite FTS5 (stdlib, zero deps) gives ranked full-text retrieval in
milliseconds, over names AND statements.

Build (after dumping shards with tools/dump_mathlib_db.py):
    python tools/premise_index.py build data/thms_types_*.tsv
Query:
    python tools/premise_index.py query "abs add le"          # by keywords
    python tools/premise_index.py goal "|a + b| ≤ |a| + |b|"  # by goal text

The `goal` mode extracts search terms from Lean goal syntax (operators ->
lemma-name vocabulary like `abs`, `add`, `le`), which is what the retrieval
agent uses.
"""

import argparse
import glob
import os
import re
import sqlite3
import sys

DB = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                  "data", "premises.sqlite")

# Lean goal syntax -> the vocabulary mathlib lemma names are built from.
SYMBOL_WORDS = [
    ("≤", "le"), ("<", "lt"), ("≥", "ge"), ("=", "eq"), ("≠", "ne"),
    ("+", "add"), ("-", "sub"), ("*", "mul"), ("/", "div"), ("^", "pow"),
    ("|", "abs"), ("∣", "dvd"), ("∈", "mem"), ("∪", "union"), ("∩", "inter"),
    ("⊆", "subset"), ("∀", ""), ("∃", "exists"), ("¬", "not"), ("∧", "and"),
    ("∨", "or"), ("→", ""), ("↔", "iff"), ("√", "sqrt"), ("∑", "sum"),
    ("∏", "prod"), ("!", "factorial"), ("ℝ", "real"), ("ℕ", "nat"),
    ("ℤ", "int"), ("ℚ", "rat"),
]


def tokenize_name(name: str):
    """Nat.Prime.dvd_choose_pow -> [nat, prime, dvd, choose, pow]"""
    parts = re.split(r"[._']", name)
    out = []
    for p in parts:
        out += re.findall(r"[A-Z]?[a-z0-9]+|[A-Z]+(?![a-z])", p)
    return [w.lower() for w in out if w]


def goal_terms(goal: str):
    """Extract lemma-name vocabulary from Lean goal text."""
    terms = []
    for sym, word in SYMBOL_WORDS:
        if sym in goal and word:
            terms.append(word)
    # identifiers appearing in the goal (Nat.succ, Finset.sum, hypotheses...)
    for ident in re.findall(r"[A-Za-z][A-Za-z0-9_.]{2,}", goal):
        terms += tokenize_name(ident)
    seen, out = set(), []
    for t in terms:
        if t not in seen and len(t) > 1:
            seen.add(t)
            out.append(t)
    return out


def build(tsv_paths):
    os.makedirs(os.path.dirname(DB), exist_ok=True)
    if os.path.exists(DB):
        os.unlink(DB)
    con = sqlite3.connect(DB)
    con.execute("CREATE VIRTUAL TABLE premises USING fts5(name, tokens, statement)")
    n = 0
    for path in tsv_paths:
        with open(path) as f:
            for line in f:
                line = line.rstrip("\n")
                if not line:
                    continue
                name, _, stmt = line.partition("\t")
                con.execute("INSERT INTO premises VALUES (?,?,?)",
                            (name, " ".join(tokenize_name(name)), stmt))
                n += 1
    con.commit()
    con.close()
    print("indexed {} theorems -> {}".format(n, DB))


def query(terms, k=10):
    con = sqlite3.connect(DB)
    q = " OR ".join('"{}"'.format(t.replace('"', "")) for t in terms)
    rows = con.execute(
        "SELECT name, statement, bm25(premises) AS score FROM premises "
        "WHERE premises MATCH ? ORDER BY score LIMIT ?", (q, k)).fetchall()
    con.close()
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["build", "query", "goal"])
    ap.add_argument("args", nargs="+")
    ap.add_argument("-k", type=int, default=10)
    a = ap.parse_args()

    if a.mode == "build":
        paths = []
        for pat in a.args:
            paths += glob.glob(pat)
        if not paths:
            sys.exit("no TSV files matched")
        build(sorted(paths))
        return

    terms = a.args if a.mode == "query" else goal_terms(" ".join(a.args))
    if a.mode == "goal":
        print("terms: {}".format(" ".join(terms)))
    for name, stmt, score in query(terms, a.k):
        print("  {:6.2f}  {}  ::  {}".format(score, name, stmt[:90]))


if __name__ == "__main__":
    main()
