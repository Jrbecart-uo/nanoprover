
def construct():
    """Product construction: the largest cap in F_3^1 is {0,1} (2 points, since
    {0,1,2} is itself a line). Taking the product over 6 coordinates gives
    2^6 = 64 points with no line — a valid but far-from-optimal cap set."""
    from itertools import product
    return [list(v) for v in product([0, 1], repeat=6)]
