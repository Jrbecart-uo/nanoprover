"""Bose optimal Sidon set: size q in Z/(q^2-1), density ->1. Then reflection."""
import math

def gf2_mul(a, b, s, q):
    (u,v),(x,y)=a,b
    return ((u*x + v*y*s) % q, (u*y + v*x) % q)

def nonresidue(q):
    rs={(i*i)%q for i in range(q)}
    for s in range(2,q):
        if s not in rs: return s
    return None

def bose_sidon(q):
    """B = {a in [0,q^2-2] : theta^a = theta + b, b in GF(q)}, Sidon mod q^2-1."""
    s=nonresidue(q)
    if s is None: return None
    n=q*q-1
    # find generator theta of GF(q^2)^* ; try element (g,1)=g+i for small g
    def order(el):
        cur=(1,0); 
        for k in range(1,n+1):
            cur=gf2_mul(cur,el,s,q)
            if cur==(1,0): return k
        return -1
    theta=None
    for g0 in range(0,q):
        el=(g0,1)
        if order(el)==n: theta=el; break
    if theta is None:
        for g0 in range(0,q):
            for g1 in range(1,q):
                el=(g0,g1)
                if order(el)==n: theta=el; break
            if theta: break
    if theta is None: return None
    # powers table: theta^a
    pows={}
    cur=(1,0)
    for a in range(n):
        pows[cur]=a
        cur=gf2_mul(cur,theta,s,q)
    # want a with theta^a = theta + b = (add b to first coord of theta)
    B=[]
    for b in range(q):
        target=((theta[0]+b)%q, theta[1])
        if target in pows:
            B.append(pows[target])
    return sorted(set(B)), n

def is_sidon_mod(B,n):
    diffs=set()
    for i in range(len(B)):
        for j in range(len(B)):
            if i!=j:
                d=(B[i]-B[j])%n
                if d in diffs: return False
                diffs.add(d)
    return True

def stats(A,N):
    A=sorted(set(A)); k=len(A)
    ss=len({a+b for a in A for b in A}); C=k*(k-1)//2
    return k, ss/C if C else 0, k/math.sqrt(N)

print(f"target 2/sqrt(3) = {2/math.sqrt(3):.4f}\n")
for q in [13,29,53,101,211,401]:
    res=bose_sidon(q)
    if res is None: print(f"q={q}: skip"); continue
    B,n=res
    if not is_sidon_mod(B,n): print(f"q={q}: not Sidon mod {n}"); continue
    # B in [0,n), n=q^2-1 ~ q^2. genuine integer Sidon set (Sidon mod n => Sidon as ints in [0,n))
    Bs=[b+1 for b in B]           # [1,n]
    M=n                            # B in [1,M]
    N=3*M                          # place in [1,N/3]
    A=Bs+[N+1-b for b in Bs]
    k,delta,r=stats(A,N)
    print(f"q={q:4d}: |B|={len(B):3d} (~sqrt(M)={math.sqrt(M):.0f})  |A|={k:4d}  "
          f"N={N}  delta={delta:.4f}  r={r:.4f}")
