"""Config C on miniF2F residuals: external proposals through the kernel filter."""
import json, os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from minif2f import parse_problems, MATHLIB

props = json.load(open(os.path.join(os.path.dirname(__file__), "minif2f_proposals.json")))
byname = {p["name"]: p for p in parse_problems()}

lines = ["import Mathlib", "set_option maxHeartbeats 800000", ""]
linemap = {}
for name, scripts in props.items():
    g = byname[name]
    for si, script in enumerate(scripts):
        start = len(lines) + 1
        if g["open"]:
            lines.append("open {} in".format(g["open"]))
        lines.append("example {} := by".format(g["sig"]))
        lines += ["  " + l for l in script.splitlines()]
        lines.append("")
        linemap[(name, si)] = (start, len(lines))

path = "/tmp/minif2f_c_probe.lean"
open(path, "w").write("\n".join(lines) + "\n")
p = subprocess.run(["lake", "env", "lean", path], cwd=MATHLIB,
                   capture_output=True, text=True, timeout=560)
err_lines = {int(m.group(1)) for m in
             re.finditer(r"probe\.lean:(\d+):\d+: error", p.stdout + p.stderr)}
solved = 0
for name, scripts in props.items():
    ok = [si for si in range(len(scripts))
          if not any(s <= ln <= e for ln in err_lines
                     for s, e in [linemap[(name, si)]])]
    print("  {:32s} {}".format(
        name, "SOLVED (attempt {})".format(ok[0] + 1) if ok else "--"))
    solved += bool(ok)
print("\nproposals solved {}/{} residuals".format(solved, len(props)))
