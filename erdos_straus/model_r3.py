"""Round 3 model: per-a success probabilities q_a(X) for primes p ≡ 1 (24) near X, and the independence model
P(a_min > A) = prod_{a<=A} (1 - q_a) versus the observed tail."""
import random, math, sys
from collections import Counter
def isprime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d=n-1; s=0
    while d%2==0: d//=2; s+=1
    for b in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(b,d,n)
        if x in (1,n-1): continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def pf(n):
    out=[]; i=2
    while i*i<=n:
        while n%i==0: out.append(i); n//=i
        i+=1 if i==2 else 2
    if n>1: out.append(n)
    return out
def works(p,a):
    x=(p+a)//4; B=p*x
    ds=[1]
    for q,e in Counter(pf(x)+[p]).items(): ds=[d*q**k for d in ds for k in range(2*e+1)]
    for d in ds:
        if d<B and (B+d)%a==0 and (B+B*B//d)%a==0: return True
    return False
def main():
    AS=list(range(3,160,4))
    random.seed(1)
    for X in (10**5,10**6,10**7,10**8,10**9):
        ps=[]
        while len(ps)<int(sys.argv[1]):
            p=random.randrange(X//2,X)//24*24+1
            if isprime(p): ps.append(p)
        W={a:[works(p,a) for p in ps] for a in AS}
        q={a:sum(W[a])/len(ps) for a in AS}
        amin=[next((a for a in AS if W[a][i]),999) for i in range(len(ps))]
        # independence prediction of P(a_min > A)
        line=[]
        for A in (3,7,11,19,31,47):
            pred=math.prod(1-q[a] for a in AS if a<=A)
            obs=sum(1 for m in amin if m>A)/len(ps)
            line.append(f'A={A}: obs {obs:.4f} indep {pred:.4f}')
        print(f'X={X:.0e}  q_3={q[3]:.3f} q_7={q[7]:.3f} q_11={q[11]:.3f} q_15={q[15]:.3f} q_19={q[19]:.3f} q_23={q[23]:.3f} q_43={q[43]:.3f} q_83={q[83]:.3f} q_155={q[155]:.3f}')
        print('    '+' | '.join(line))
        sys.stdout.flush()

if __name__ == '__main__':
    main()
