"""CALIBRATION PROBLEM — cap sets in dimension 6.  NOT an open problem.

A cap set in F_3^n is a subset with no three distinct points summing to 0 mod 3
(i.e. no three in a line). The maximum size is KNOWN exactly for n = 6: it is
112 (Potechin 2008). That is precisely why this file exists.

This is the instrument's calibration weight. Before pointing the engine at
anything open we make it search a space whose true answer is already known: if
the engine cannot rediscover 112, its verdict on an open problem is worth
nothing. And if the evaluator ever reports MORE than 112, the evaluator is
broken — that number is a mathematical fact, not a leaderboard.

(Cap sets are also the problem FunSearch actually beat, at n = 8. We are not
attempting that here; we are checking our scales are true.)
"""

STATEMENT = """
A CAP SET in F_3^n is a set S of vectors in {0,1,2}^n containing no three
DISTINCT points x, y, z with x + y + z = 0 (mod 3) — equivalently, no three
collinear points.  Note x+y+z=0 mod 3 with x,y,z distinct is the "line"
condition; a point is never a line with itself here.

n = 6.  The ambient space has 3^6 = 729 points.
Return the largest cap set you can, as a list of 6-element lists over {0,1,2}.
"""

TARGET = "maximise |S| for n = 6"
RECORD = "112 (Potechin 2008) — this is the PROVEN MAXIMUM, not a record to beat"

N = 6


def _is_cap(S):
    """No three distinct points on a line. Third point of any pair is forced:
    x + y + z = 0 mod 3  =>  z = -(x+y) = (2x + 2y) mod 3, so we only need to
    check whether that forced z is present and distinct from x and y."""
    pts = {tuple(v) for v in S}
    L = list(pts)
    for i in range(len(L)):
        for j in range(i + 1, len(L)):
            x, y = L[i], L[j]
            z = tuple((-(a + b)) % 3 for a, b in zip(x, y))
            if z != x and z != y and z in pts:
                return False
    return True


def _valid_points(S):
    if not isinstance(S, list):
        return False, "not a list"
    for v in S:
        if not isinstance(v, list) or len(v) != N:
            return False, f"not a {N}-vector: {v!r}"
        if any(c not in (0, 1, 2) for c in v):
            return False, f"entries must be in {{0,1,2}}: {v!r}"
    if len({tuple(v) for v in S}) != len(S):
        return False, "duplicate points"
    return True, ""


def evaluate(obj):
    """Score = |S| if S is a genuine cap set, else None (invalid)."""
    ok, msg = _valid_points(obj)
    if not ok:
        return {"score": None, "error": msg}
    if not _is_cap(obj):
        return {"score": None, "error": "contains a line (three collinear points)"}
    return {"score": len(obj), "detail": f"valid cap set of size {len(obj)} in F_3^{N}"}


def beats_record(score):
    # 112 is the proven maximum. Anything above it means WE have a bug.
    return score is not None and score > 112


def verify(obj):
    """Independent, deliberately naive O(|S|^3) check — no cleverness."""
    pts = [tuple(v) for v in obj]
    n = len(pts)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                if all((pts[i][d] + pts[j][d] + pts[k][d]) % 3 == 0
                       for d in range(N)):
                    return False, f"line found: {pts[i]}, {pts[j]}, {pts[k]}"
    return True, f"no line among {n} points (checked all C({n},3) triples)"


def verify_champion(src):
    g = {}
    exec(compile(src, "champ", "exec"), g)
    obj = g["construct"]()
    ok, msg = _valid_points(obj)
    if not ok:
        return False, msg
    return verify(obj)


# The published lower-bound construction, as a starting lineage: the product of
# the optimal n=1 cap {0,1,2}? No — that is the whole line. In F_3^1 the largest
# cap is 2 points. The naive product construction gives 2^6 = 64.
SEED = '''
def construct():
    """Product construction: the largest cap in F_3^1 is {0,1} (2 points, since
    {0,1,2} is itself a line). Taking the product over 6 coordinates gives
    2^6 = 64 points with no line — a valid but far-from-optimal cap set."""
    from itertools import product
    return [list(v) for v in product([0, 1], repeat=6)]
'''
