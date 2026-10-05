"""Round 2: wilder hypotheses on primes p ≡ 1 (mod 24) (first K primes of the es_scan CSV)."""
import csv, math, sys
from collections import Counter, defaultdict
CSV=sys.argv[1]; K=int(sys.argv[2])
rows=[(int(r['p']),int(r['a_min']),int(r['nwork'])) for r in csv.DictReader(open(CSV))][:K]
def pf(n):
    out=[]; i=2
    while i*i<=n:
        while n%i==0: out.append(i); n//=i
        i+=1
    if n>1: out.append(n)
    return out
def divisors_sq(n):
    f=Counter(pf(n)); ds=[1]
    for q,e in f.items():
        ds=[d*q**k for d in ds for k in range(2*e+1)]
    return ds
def two_unit(A,B):
    """A/B = 1/y+1/z with y<z? via d | B^2, d ≡ -B mod A, d < B."""
    for d in divisors_sq(B):
        if d<B and (B+d)%A==0 and (B+B*B//d)%A==0: return d
    return None
def typeI(p,XMAX=60):
    for xp in range(1,XMAX+1):
        A=4*xp-1; B=p*xp
        # d must divide B^2 and avoid giving y or z divisible by p: just require gcd(d,p)=1 and d|xp^2
        for d in divisors_sq(xp):
            if d<B and (B+d)%A==0 and (B+B*B//d)%A==0: return xp
    return None
def typeII(p,S=40):
    best=None
    for yp in range(1,S):
        for zp in range(yp+1,S):
            m=4*yp*zp-yp-zp
            if (p*yp*zp)%m==0:
                x=p*yp*zp//m
                if x<p*yp: return (yp,zp)
    return None
def leg(a,q): return pow(a%q,(q-1)//2,q)
res=defaultdict(lambda:[0,None])
def test(name,ok,p,info=''):
    r=res[name]; r[0]+=1
    if not ok and r[1] is None: r[1]=(p,info)
for (p,a,nw) in rows:
    x3,x7,x11=(p+3)//4,(p+7)//4,(p+11)//4
    t1=typeI(p); t2=typeII(p)
    test('W1 a Type I solution (p | x only) exists with x\' <= 60',t1 is not None,p)
    test('W2 a Type II solution (p | y, p | z) exists with y\',z\' < 40',t2 is not None,p)
    test('W3 a_min >= 23 => p is a QR mod 5, 7, 11, 13',a<23 or all(leg(p,q)==1 for q in (5,7,11,13)),p,a)
    test('W4 a_min <= smallest a (=3 mod 4) with (p+a)/4 composite',a<=min(b for b in range(3,400,4) if len(pf((p+b)//4))>1),p,a)
    test('W5 nwork(<=400) >= ln p',nw>=math.log(p),p,nw)
    f7=pf(x7)
    crit7=any(leg(q,7)==6 for q in f7 if q!=7) or leg(p,7)==6
    test('W6 (a_min>3) : a=7 works  <=>  x7 or p has a prime factor that is a QNR mod 7',(a<=7)==(crit7 or a==3) if a!=3 else True,p,a)
    f11=pf(x11)
    crit11=any(leg(q,11)==10 for q in f11 if q!=11) or leg(p,11)==10
    test('W7 (a_min>7) : a=11 works <= some prime factor of x11 or p is a QNR mod 11',(not crit11) or a<=11,p,a)
    test('W8 a_min <= 3 + 4 * (number of prime factors of x3 that are = 1 mod 3)',a<=3+4*sum(1 for q in pf(x3) if q%3==1),p,a)
    test('W9 x3 prime => a_min <= 7',len(pf(x3))>1 or a<=7,p,a)
    test('W10 a_min <= 7 unless p = 1 mod 7*? (p QR mod 7)',a<=7 or leg(p,7)==1,p,a)
for name,(n,cex) in res.items():
    print(('SURVIVES ' if cex is None else 'DEAD     ')+name+f'   [tested {n}]'+('' if cex is None else f'  first cex p={cex[0]} info={cex[1]}'))
