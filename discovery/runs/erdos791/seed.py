
import time

KOHONEN_I = [0, 5] + list(range(112, 138, 5))
KOHONEN_J = list(range(10, 107, 6))
KOHONEN_K = list(range(0, 5)) + list(range(224, 230)) + list(range(367, 373))


def m_of(I, J, K):
    IJ = {a + b for a in I for b in J}
    IK = {a + b for a in I for b in K}
    JK = {a + b for a in J for b in K}
    sq = IJ | IK
    m = 0
    while m in sq or (m in JK and (m - 1) in JK):
        m += 1
    return m


def ratio(I, J, K):
    l = len(I) + len(J) + len(K)
    return m_of(I, J, K) / (l * l)


def search(prev_best, deadline, rng):
    """SEED: Kohonen's placement + naive random single-element hill climbing.

    Deliberately weak — it only jiggles one integer at a time and never changes
    the SHAPE of the placement. Everything interesting lives in the shape."""
    if prev_best:
        I, J, K = list(prev_best["I"]), list(prev_best["J"]), list(prev_best["K"])
    else:
        I, J, K = list(KOHONEN_I), list(KOHONEN_J), list(KOHONEN_K)
    best = (I[:], J[:], K[:])
    bs = ratio(*best)

    while time.time() < deadline:
        I, J, K = [list(x) for x in best]
        tgt = rng.choice([I, J, K])
        if not tgt:
            continue
        i = rng.randrange(len(tgt))
        tgt[i] = max(0, tgt[i] + rng.choice([-3, -2, -1, 1, 2, 3]))
        cand = (sorted(set(I)), sorted(set(J)), sorted(set(K)))
        if any(len(x) == 0 for x in cand):
            continue
        r = ratio(*cand)
        if r >= bs:
            best, bs = cand, r
    return {"I": best[0], "J": best[1], "K": best[2]}
