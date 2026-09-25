#!/usr/bin/env python3
"""Check that every solved Putnam file states EXACTLY the PutnamBench theorem.

For each bench/solved_putnam/NAME.txt: the text from `theorem NAME` up to the first `:=`
(whitespace-normalized) must equal PutnamBench's, and PutnamBench's `open ...` line must be
present (KNOWN_TRAPS: `open Nat` changes name resolution, so proofs must check under it).
Definitions the statement depends on (`abbrev`/`def` answers) are compared too.

  python3 tools/verify_scalps.py [--kernel] [NAME ...]

--kernel rebuilds each scalp FROM PutnamBench's own file and kernel-checks it via the REPL
daemon (tools/repl.py): script-only files (July pipeline) are spliced in place of PutnamBench's
`sorry`; full files get PutnamBench's `open` line inserted. Must PASS with axioms ⊆
{propext, Classical.choice, Quot.sound}.
"""
import json
import subprocess
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOLVED = os.path.join(REPO, "bench", "solved_putnam")
PB = os.path.join(REPO, "PutnamBench", "lean4", "src")


def norm(s):
    return " ".join(s.split())


def stmt(src, name):
    m = re.search(r"theorem\s+" + re.escape(name) + r"\b(.*?):=", src, re.S)
    return norm(m.group(1)) if m else None


def opens(src):
    return [norm(l) for l in src.splitlines() if l.startswith("open ")]


def answers(src):
    """abbrev/def blocks that the statement may mention (e.g. `putnam_XXXX_solution`)."""
    return {m.group(1): norm(m.group(2)) for m in
            re.finditer(r"^(?:noncomputable )?(?:abbrev|def)\s+(\S+)(.*?)(?=^\S)", src, re.S | re.M)}


def check(name):
    mine = open(os.path.join(SOLVED, name + ".txt")).read()
    ref = open(os.path.join(PB, name + ".lean")).read()
    problems = []
    if stmt(mine, name) != stmt(ref, name):
        problems.append("statement differs")
    for o in opens(ref):
        if o not in opens(mine):
            problems.append(f"missing `{o}`")
    ra, ma = answers(ref), answers(mine)
    for k, v in ra.items():
        if k.startswith(name) and ma.get(k) is not None and ma[k].split(":=")[0] != v.split(":=")[0]:
            problems.append(f"answer `{k}` signature differs")
    if "sorry" in re.sub(r"--.*", "", mine):
        problems.append("contains sorry")
    return problems


def rebuilt(name):
    mine = open(os.path.join(SOLVED, name + ".txt")).read()
    ref = open(os.path.join(PB, name + ".lean")).read()
    if stmt(mine, name) is None:            # tactic script only: splice into PutnamBench
        body = "\n".join("  " + l for l in mine.strip().splitlines())
        i = ref.rindex("sorry")
        head = ref[:i].rstrip()
        assert head.endswith(":="), name
        return head + " by\n" + body + f"\n\n#print axioms {name}\n"
    lines = mine.splitlines()
    for o in reversed(opens(ref)):
        if o not in opens(mine):
            k = max(i for i, l in enumerate(lines) if l.startswith("import")) + 1
            lines.insert(k, o)
    src = "\n".join(lines)
    if f"#print axioms {name}" not in src:
        src += f"\n#print axioms {name}\n"
    return src


def kernel(name):
    r = subprocess.run([sys.executable, os.path.join(REPO, "tools", "repl.py"), "check", "-"],
                       input=rebuilt(name), capture_output=True, text=True)
    out = r.stdout
    if not out.startswith("PASS"):
        errs = [m["data"][:120] for m in json.loads(out[out.index("{"):]).get("messages", [])
                if m["severity"] == "error"] if "{" in out else [out[:200]]
        return [f"kernel FAIL: {errs[:2]}"]
    ax = re.search(r"depends on axioms: \[([^\]]*)\]", out)
    extra = set(x.strip() for x in ax.group(1).split(",")) - {"propext", "Classical.choice", "Quot.sound"} if ax else set()
    return [f"nonstandard axioms {sorted(extra)}"] if extra else []


def main():
    args = sys.argv[1:]
    use_kernel = "--kernel" in args
    args = [a for a in args if a != "--kernel"]
    names = args or sorted(f[:-4] for f in os.listdir(SOLVED) if f.endswith(".txt"))
    bad = 0
    for n in names:
        p = check(n)
        script_only = stmt(open(os.path.join(SOLVED, n + ".txt")).read(), n) is None
        if script_only:   # statement comes from PutnamBench itself when rebuilt
            p = [x for x in p if x != "statement differs" and not x.startswith("missing `open")]
        elif use_kernel:  # opens are inserted by rebuilt(); the kernel run is the real test
            p = [x for x in p if not x.startswith("missing `open")]
        if use_kernel and not [x for x in p if x == "statement differs"]:
            p += kernel(n)
        bad += bool(p)
        print(f"{'ok ' if not p else 'BAD'} {n}" + (": " + "; ".join(p) if p else ""))
    print(f"{len(names) - bad}/{len(names)} scalp statements match PutnamBench")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
