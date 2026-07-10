"""
Dump the mathlib theorem database -- the "existing theorems" an agent can
build on -- straight from Lean's compiled environment.

    python tools/dump_mathlib_db.py                         # all ~319k names
    python tools/dump_mathlib_db.py --prefix Nat            # one namespace
    python tools/dump_mathlib_db.py --prefix Nat --types    # names + statements

Names-only over all of mathlib takes ~10s. --types pretty-prints each
statement (what you feed an LLM for premise selection) and is slower, so pair
it with --prefix for the namespaces you care about.

Requires: mathlib4/ checkout with the prebuilt cache (setup.sh --mathlib).
"""

import argparse
import os
import subprocess
import tempfile

MATHLIB = os.environ.get("NANOPROVER_MATHLIB_DIR",
    os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                 "mathlib4"))

SCRIPT = r'''import Mathlib
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let h ← IO.FS.Handle.mk "{out}" IO.FS.Mode.write
  let prefixFilter := "{prefix}"
  let mut n := 0
  let mut i := 0
  for (name, info) in env.constants.toList do
    if ({thmonly} || info.isTheorem) && !name.isInternalDetail then
      i := i + 1
      let s := name.toString
      if (prefixFilter == "" || s.startsWith prefixFilter) && i % {mod} == {shard} then
        {emit}
        n := n + 1
  logInfo s!"dumped {{n}} theorems"
'''

EMIT_NAMES = 'h.putStrLn s'
EMIT_TYPES = '''let ty ← liftTermElabM do
          let fmt ← Meta.ppExpr info.type
          pure (toString fmt)
        h.putStrLn (s ++ "\\t" ++ ty.replace "\\n" " ")'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--prefix", default="", help="namespace filter, e.g. Nat")
    ap.add_argument("--all-constants", action="store_true",
                    help="include defs/abbrevs/instances, not just theorems")
    ap.add_argument("--types", action="store_true",
                    help="include pretty-printed statements (slower)")
    ap.add_argument("--out", default="mathlib_theorems.txt")
    ap.add_argument("--shard", type=int, default=0, help="shard index (with --num-shards)")
    ap.add_argument("--num-shards", type=int, default=1)
    args = ap.parse_args()

    out = os.path.abspath(args.out)
    src = SCRIPT.format(out=out, prefix=args.prefix,
                        thmonly=('true' if args.all_constants else 'false'),
                        mod=args.num_shards, shard=args.shard,
                        emit=EMIT_TYPES if args.types else EMIT_NAMES)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(src)
        path = f.name
    try:
        p = subprocess.run(["lake", "env", "lean", path], cwd=MATHLIB,
                           capture_output=True, text=True, timeout=1800)
        print((p.stdout + p.stderr).strip())
        if p.returncode != 0:
            raise SystemExit(1)
    finally:
        os.unlink(path)
    print("wrote", out)


if __name__ == "__main__":
    main()
