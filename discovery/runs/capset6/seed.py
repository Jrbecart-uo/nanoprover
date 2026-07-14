
import time
from itertools import product


def search(prev_best, deadline, rng):
    """SEED HEURISTIC — deliberately weak, so there is headroom to evolve into.

    Randomised greedy restarts until the deadline. Keeps prev_best if it cannot
    beat it, so the lineage can never go backwards."""
    P = [tuple(v) for v in product(range(3), repeat=6)]
    idx = {p: i for i, p in enumerate(P)}
    third = [[0] * len(P) for _ in range(len(P))]
    for i, x in enumerate(P):
        for j, y in enumerate(P):
            if i != j:
                third[i][j] = idx[tuple((-(a + b)) % 3 for a, b in zip(x, y))]

    best = [tuple(v) for v in prev_best] if prev_best else []
    while time.time() < deadline:
        S, bad = [], set()
        order = list(range(len(P)))
        rng.shuffle(order)
        for p in order:
            if p in bad:
                continue
            for q in S:
                bad.add(third[p][q])
            S.append(p)
        if len(S) > len(best):
            best = [P[i] for i in S]
    return [list(v) for v in best]
