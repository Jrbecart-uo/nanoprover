#!/usr/bin/env bash
# Detached, resumable build of openai/NavierStokesAndEuler. Log: ns_build.log
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=4
cd "$(dirname "$0")/NavierStokesAndEuler"
echo "[$(date +%T)] cache get" 
lake exe cache get || { echo "CACHE FAILED"; exit 1; }
echo "[$(date +%T)] build start"
/usr/bin/time -v lake build NavierStokes Euler ComparatorChallenges
echo "[$(date +%T)] build exit $?"
