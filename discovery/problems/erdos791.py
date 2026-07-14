"""ERDOS #791 — Rohrbach's problem: finite additive 2-bases.  GENUINELY OPEN.

    A set A of non-negative integers is an additive 2-basis with range n if
    A + A contains 0,1,...,n.  Let n(k) = the largest range achievable with
    |A| = k.  How large is liminf n(k)/k^2 ?

    known:   0.2891156... <= liminf n(k)/k^2 <= 0.4909...
             ^^^^^^^^^ THE RECORD WE ARE ATTACKING

The lower bound is a CONSTRUCTION, and beating it is a finite, checkable act.

  Mrose   1979 :  2/7      = 0.2857142...
  Kohonen 2017 :  85/294   = 0.2891156...   <- current world record, 9 years old

WHY THIS TARGET (the honest case)

  * The compute moat does not exist. Kohonen, in his own paper: "With a simple
    computer program we searched through placements of size l <= 17, but found
    none with m/l^2 > 2/7. However, from a combination of computer-based search
    and manual design, we have the following result" — and the result is at
    l = 42. So the exhaustive frontier is l <= 17, and the record was set by ONE
    PERSON, PARTLY BY HAND. This is idea-bottlenecked, not FLOP-bottlenecked.
  * The evaluator costs 28 microseconds. We can try millions of placements.
  * It sits outside the AlphaEvolve footprint (they did the DIFFERENCE-basis
    sibling, B-B, not this one).
  * Crucially the ANSATZ ITSELF is a human choice — three segment shapes
    (V, H, S) and a placement (I, J, K). An LLM can REWRITE the ansatz, not
    merely re-tune it. That is an idea-move no exhaustive search over Kohonen's
    parametrisation can reach.

THE CONSTRUCTION (Kohonen 2017, verbatim from arXiv:1606.04770)

  For t >= 2 the three ELEMENTARY SEGMENTS are
      V = [0, t]                    (a vertical line, |V| = t+1)
      H = {0, t, 2t, ..., t^2 - t}  (a horizontal line, |H| = t)
      S = {0, t+1, ..., t^2 - 1}    (a slanted line,   |S| = t)
  under the visualisation i -> (floor(i/t), i mod t).  Given placements
  I, J, K (sets of non-negative integers) the basis is

      A = (V + t^2 . I)  u  (H + t^2 . J)  u  (S + t^2 . K)

  Write Q = [0, t^2 - 1] (a "square") and P = H + S (a "parallelogram"). Then
      V+H  and  V+S  each contain Q          -> squares at (I+J) and (I+K)
      P and P+t^2 together contain Q + t^2   -> a square at s needs BOTH
                                                s and s-1 in (J+K)
  so, with l = |I|+|J|+|K| and m = the number of consecutive squares covered
  starting from 0, the basis has size k <= l(t+1) and range n >= m t^2 - 1,
  giving  liminf n(k)/k^2 >= m/l^2  (the (t/(t+1))^2 loss vanishes as t -> oo).

  ANY (I, J, K) WITH m/l^2 > 85/294 IS A NEW WORLD RECORD.

  Concretely: l=43 needs m >= 535;  l=50 needs m >= 723;  l=60 needs m >= 1041.

THE ADVERSARY IS THE SCORER.  The fast score below uses Kohonen's covering
CRITERION. If I have misread the paper, a "record" found against it is worthless.
So `verify_champion` ignores the criterion entirely: it MATERIALISES the actual
integer set A at a concrete t, computes A+A by brute force, and checks
{0,...,n} really is covered. The two share no logic. If they ever disagree, the
criterion is wrong and the record is not a record.
"""

from fractions import Fraction

RECORD_FRAC = Fraction(85, 294)          # Kohonen 2017
PREV_RECORD = Fraction(2, 7)             # Mrose 1979

STATEMENT = """
Choose three FINITE SETS of non-negative integers I, J, K.
Let l = |I| + |J| + |K|.

Define the covered "squares": integer s >= 0 is COVERED iff
    s in (I+J)  or  s in (I+K)                      [a square tile]
 or (s in (J+K) and s-1 in (J+K))                   [two consecutive parallelograms]
where X+Y = {x+y : x in X, y in Y}.

Let m = the number of CONSECUTIVE covered squares starting at 0
        (i.e. the least s that is NOT covered).

MAXIMISE  m / l^2 .

This is exactly Kohonen's reduction of Erdos #791 (Rohrbach's problem): any
placement with m/l^2 > 85/294 = 0.2891156... is a NEW WORLD RECORD on the
liminf n(k)/k^2 lower bound for finite additive 2-bases.

Return {"I": [...], "J": [...], "K": [...]} as lists of non-negative integers.
Scale is free: only the RATIO m/l^2 matters, so you may use as many segments as
you like — but every extra element of I, J or K costs you l, quadratically.

EXPERT HINTS (from Kohonen's own "further improvement" section — the literature
is emphatic that a real hint is worth more than any amount of extra sampling):

1. THERE IS ENORMOUS HEADROOM. Kohonen proves a CEILING for this very ansatz:
       m/l^2  <=  (|I||J| + |I||K| + |J||K|) / l^2  <=  1/3.
   The record is 0.2891. The ceiling is 0.3333. The record is NOT known to be
   optimal — Kohonen simply stopped searching.

2. THE SPLIT IS LOPSIDED, AND THAT COSTS HIM. Kohonen uses |I|=8, |J|=17,
   |K|=17. For that split the counting ceiling is only
       (8*17 + 8*17 + 17*17)/42^2 = 561/1764 = 0.318,
   and he attains 510/561 = 91% of it. A BALANCED split (|I|=|J|=|K|=l/3) has
   the full ceiling 1/3. Merely reaching 91% efficiency at a balanced split
   would give 0.91 * 0.3333 = 0.303 — comfortably past the record.
   So: WHY is the efficient placement so unbalanced? Is that forced by the
   asymmetric roles (I pairs with both J and K to make squares; J and K only
   make parallelograms, and those need CONSECUTIVE pairs), or is it merely the
   shape Kohonen's hand-design happened to land on? Attack that question.

3. THE REAL OBJECTIVE IS EFFICIENCY, NOT m. Maximise
       m / (|I||J| + |I||K| + |J||K|)      [how much of the ceiling you capture]
   while keeping the split balanced. Waste = squares covered twice, or
   parallelograms that never find their consecutive partner.

4. EXHAUSTIVE SEARCH HAS NEVER PASSED l <= 17. Everything above l=17 is
   unexplored except by one person's hand-design. The space is wide open.
"""

TARGET = "maximise m / l^2   (l = |I|+|J|+|K|, m = consecutive squares covered from 0)"
RECORD = ("85/294 = 0.28911564  (Kohonen 2017, l=42, m=510). "
          "Previous: 2/7 = 0.28571429 (Mrose 1979). "
          "Exhaustive search has only ever reached l <= 17.")


# ------------------------------------------------------------------ fast score
def _m_of(I, J, K):
    """Number of consecutive covered squares from 0. This is the hot loop."""
    IJ = {a + b for a in I for b in J}
    IK = {a + b for a in I for b in K}
    JK = {a + b for a in J for b in K}
    sq = IJ | IK
    m = 0
    while m in sq or (m in JK and (m - 1) in JK):
        m += 1
    return m


def _clean(obj):
    if not isinstance(obj, dict):
        return None, "must return {'I': [...], 'J': [...], 'K': [...]}"
    out = {}
    for key in ("I", "J", "K"):
        if key not in obj:
            return None, f"missing '{key}'"
        v = obj[key]
        if not isinstance(v, (list, tuple)) or not v:
            return None, f"'{key}' must be a non-empty list"
        try:
            s = sorted({int(x) for x in v})
        except (TypeError, ValueError):
            return None, f"'{key}' must contain integers"
        if any(x < 0 for x in s):
            return None, f"'{key}' must be non-negative"
        out[key] = s
    return out, ""


def evaluate(obj):
    d, err = _clean(obj)
    if d is None:
        return {"score": None, "error": err}
    I, J, K = d["I"], d["J"], d["K"]
    l = len(I) + len(J) + len(K)
    m = _m_of(I, J, K)
    ratio = Fraction(m, l * l)
    tag = ""
    if ratio > RECORD_FRAC:
        tag = "  *** EXCEEDS KOHONEN 85/294 — VERIFY BEFORE BELIEVING ***"
    elif ratio > PREV_RECORD:
        tag = "  (beats Mrose 2/7, below Kohonen)"
    return {"score": float(ratio), "object": d,
            "detail": f"l={l} m={m}  m/l^2 = {m}/{l*l} = {float(ratio):.9f}{tag}"}


def beats_record(score):
    return score is not None and Fraction(score).limit_denominator(10**9) > RECORD_FRAC


# ------------------------------------- independent ground-truth verification
def materialise(I, J, K, t):
    """Build the ACTUAL integer set A = (V + t^2 I) u (H + t^2 J) u (S + t^2 K)."""
    V = list(range(0, t + 1))                   # [0, t]              |V| = t+1
    H = list(range(0, t * t - t + 1, t))        # {0, t, ..., t^2-t}  |H| = t
    S = list(range(0, t * t, t + 1))            # {0, t+1, ..., t^2-1} |S| = t
    A = set()
    for i in I:
        A |= {v + t * t * i for v in V}
    for j in J:
        A |= {h + t * t * j for h in H}
    for k in K:
        A |= {s + t * t * k for s in S}
    return A


def verify_ground_truth(I, J, K, t):
    """THE REAL CHECK. Ignores Kohonen's criterion entirely: build A, compute
    A+A honestly, and see how far the run of covered integers actually goes.

    Returns (n, k, ratio) where n = largest integer with [0..n] subset A+A."""
    A = sorted(materialise(I, J, K, t))
    k = len(A)
    m = _m_of(I, J, K)
    limit = m * t * t          # we claim [0, m t^2 - 1] is covered
    hit = bytearray(limit + 2)
    for i, a in enumerate(A):
        if a > limit:
            break
        for b in A[i:]:
            s = a + b
            if s > limit:
                break
            hit[s] = 1
    n = -1
    while n + 1 <= limit and hit[n + 1]:
        n += 1
    return n, k, Fraction(n, k * k)


def verify_champion(src):
    """Re-run the champion's search program, then check its output the hard way."""
    import json
    import time
    import random
    g = {}
    exec(compile(src, "champ", "exec"), g)
    obj = g["search"](None, time.time() + 120, random.Random(0))
    d, err = _clean(obj)
    if d is None:
        return False, err
    I, J, K = d["I"], d["J"], d["K"]
    l = len(I) + len(J) + len(K)
    m = _m_of(I, J, K)
    claim = Fraction(m, l * l)

    # ground truth at a concrete t: does A+A REALLY cover [0, m t^2 - 1]?
    t = 40
    n, k, real = verify_ground_truth(I, J, K, t)
    expected_n = m * t * t - 1
    if n < expected_n:
        return False, (f"CRITERION IS WRONG or placement invalid: claimed m={m} "
                       f"squares (n >= {expected_n}) but A+A only covers [0,{n}]")
    msg = (f"claimed m/l^2 = {m}/{l*l} = {float(claim):.9f}\n"
           f"  materialised at t={t}: |A|={k}, A+A covers [0,{n}] "
           f"(needed [0,{expected_n}]) -> n/k^2 = {float(real):.6f}\n"
           f"  (finite n/k^2 sits below the asymptotic ratio by (t/(t+1))^2 "
           f"= {float(Fraction(t, t+1)**2):.4f}; the ASYMPTOTIC claim is {float(claim):.9f})\n"
           f"  vs Kohonen 85/294 = {float(RECORD_FRAC):.9f}")
    if claim > RECORD_FRAC:
        msg += "\n  *** THIS IS A NEW WORLD RECORD ON ERDOS #791 ***"
    return True, msg


# ------------------------------------------------------------------- the seed
# Kohonen's own placement, as the incumbent to be beaten. Starting the lineage
# from the record (rather than from nothing) is the "expert hint" that the
# literature says is worth more than any amount of extra sampling.
SEED = '''
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
'''


def verify(obj):
    """Independent check of a placement, exact arithmetic, no shortcuts."""
    d, err = _clean(obj)
    if d is None:
        return False, err
    n, k, real = verify_ground_truth(d["I"], d["J"], d["K"], 30)
    m = _m_of(d["I"], d["J"], d["K"])
    if n < m * 900 - 1:
        return False, f"criterion overclaims: A+A covers only [0,{n}]"
    return True, f"materialised basis confirms m={m} squares covered"
