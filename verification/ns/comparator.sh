#!/usr/bin/env bash
# Independent Comparator check of openai/NavierStokesAndEuler in a FRESH clone where the
# solution has never been built outside the sandbox. Log: ns_comparator.log
T=/home/jbecart/tmp/mathTest/nanoprover/external
export PATH="$T/tools/bin:$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin"
cd "$T/ns_fresh"
git status --porcelain; git rev-parse HEAD
sha256sum ComparatorChallenges/*.lean ComparatorChallenges/*.json
for cfg in ComparatorChallenges/NavierStokes.json ComparatorChallenges/Euler.json; do
  echo "[$(date +%T)] === comparator $cfg"
  systemd-run --user --wait --pipe --collect --property=RestrictAddressFamilies=~AF_UNIX \
    -E PATH="$PATH" -E LEAN_NUM_THREADS=4 --working-directory "$(pwd)" -- \
    bash -c "lake env .lake/packages/Comparator/.lake/build/bin/comparator $cfg; echo COMPARATOR_EXIT=\$?"
  echo "[$(date +%T)] === done $cfg"
done
