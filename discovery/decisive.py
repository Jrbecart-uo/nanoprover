"""Large-q decisive test. Track delta for several alpha as N grows a lot.
Expert prior: only alpha<=1/3 is asymptotically quasi-Sidon; alpha>1/3 slowly
degrades. If the alpha=1/2.7 delta keeps DROPPING at large q, it's an illusion."""
import math
from bose import bose_sidon

def get_bose(q):
    r = bose_sidon(q)
    return ([b+1 for b in r[0]], r[1]) if r else (None,None)

def delta_r(B, N):
    A = sorted(set([b for b in B if b<=N] + [N+1-b for b in B if 1<=N+1-b<=N]))
    k=len(A); ss=len({a+b for a in A for b in A}); C=k*(k-1)//2
    return (ss/C if C else 0), k/math.sqrt(N)

alphas = [3.0, 2.85, 2.7, 2.5]
print(f"  {'q':>5} {'|B|':>5} |" + "".join(f"  1/{a}: delta    r  " for a in alphas))
for q in [211, 401, 601, 1009, 2003, 4001]:
    B,n = get_bose(q)
    if B is None: continue
    row=f"  {q:>5} {len(B):>5} |"
    for a in alphas:
        d,r = delta_r(B, int(a*n))
        row += f"  {d:.5f} {r:.4f} "
    print(row)
    import sys; sys.stdout.flush()
print()
print("  1/3.0 is the known bound (r=1.1547, delta->1).")
print("  If 1/2.7 delta keeps dropping (0.9994 -> lower) as q grows -> ILLUSION.")
