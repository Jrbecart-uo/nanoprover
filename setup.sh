#!/usr/bin/env bash
# nanoprover setup: elan (Lean toolchain manager) + python venv + demo Lean repo.
set -euo pipefail
cd "$(dirname "$0")"

echo "== 1/4 elan (Lean toolchain manager) =="
if command -v elan >/dev/null 2>&1 || [ -x "$HOME/.elan/bin/elan" ]; then
  echo "   elan already installed"
else
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"

echo "== 2/4 python venv =="
if [ ! -d .venv ]; then python3 -m venv .venv; fi
. .venv/bin/activate
pip install -q --upgrade pip
pip install -q anthropic          # only needed for the Claude agent; core demos run without it
# Optional (heavy; needed only for LeanDojoEnv interactive proof states):
#   pip install lean-dojo

echo "== 3/4 demo Lean repo (lean4-example, pins Lean v4.20.0) =="
if [ ! -d lean4-example ]; then
  git clone -q --depth 1 https://github.com/yangky11/lean4-example
fi

echo "== 4/4 warm the Lean toolchain (first run downloads ~300MB) =="
( cd lean4-example && lean --version )

echo
echo "Done. Try:"
echo "  source .venv/bin/activate && export PATH=\"\$HOME/.elan/bin:\$PATH\""
echo "  python sherpa.py                  # prove a theorem turn-by-turn"
echo "  python core/real_run.py           # automated search, real kernel"
echo "  python collatz/outer_loop.py      # watch the kernel filter proposed lemmas"
