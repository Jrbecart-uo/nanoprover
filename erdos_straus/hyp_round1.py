"""Round 1 hypotheses for primes p ≡ 1 (mod 24), tested on es_scan output (CSV path argv[1])."""
import csv, math, sys
from collections import Counter
rows=[(int(r['p']),int(r['a_min']),int(r['e']),int(r['dprime']),int(r['nwork']),[int(r[k]) for k in ('a1','a2','a3','a4') if int(r[k])>0]) for r in csv.DictReader(open(sys.argv[1]))]
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def pf(n):
    out=set(); i=2
    while i*i<=n:
        while n%i==0: out.add(i); n//=i
        i+=1
    if n>1: out.add(n)
    return out
def leg(a,p): return pow(a,(p-1)//2,p)
def smallest_qnr(p):
    q=2
    while leg(q,p)==1: q+=1
    return q
def smallest_q3mod4_nonres(p):
    q=3
    while not (isprime(q) and q%4==3 and leg(p%q,q)==q-1): q+=4
    return q
H={}
H['H1 a_min = 3 always']=lambda p,a,e,d,nw,al: a==3
H['H2 a_min <= 50']=lambda p,a,e,d,nw,al: a<=50
H['H3 a_min <= 2 ln p']=lambda p,a,e,d,nw,al: a<=2*math.log(p)
H['H4 a_min <= (ln p)^2']=lambda p,a,e,d,nw,al: a<=math.log(p)**2
H['H5 a_min is prime']=lambda p,a,e,d,nw,al: isprime(a)
H['H6 witness at a_min avoids p (e=0)']=lambda p,a,e,d,nw,al: e==0
H['H7 >= 2 working a <= 400']=lambda p,a,e,d,nw,al: nw>=2
H['H8 a_min=3 iff (p+3)/4 has a prime factor = 2 mod 3']=lambda p,a,e,d,nw,al: (a==3)==any(q%3==2 for q in pf((p+3)//4))
H['H9 a_min <= 4*nqr(p) - 1  (nqr = least quadratic non-residue)']=lambda p,a,e,d,nw,al: a<=4*smallest_qnr(p)-1
H['H10 a_min <= least prime q=3 mod 4 with p a non-residue mod q']=lambda p,a,e,d,nw,al: a<=smallest_q3mod4_nonres(p)
H['H11 a_min <= 7 or p+1 has a prime factor = 3 mod 4']=lambda p,a,e,d,nw,al: a<=7 or any(q%4==3 for q in pf(p+1))
H['H12 some working a <= 400 is prime']=lambda p,a,e,d,nw,al: any(isprime(x) for x in al)
H['H13 a_min != 27 (27 is never minimal)']=lambda p,a,e,d,nw,al: a!=27
H['H14 a_min != 15']=lambda p,a,e,d,nw,al: a!=15
H['H15 a_min <= 3*sqrt(ln p)*ln ln p ... (wild slow growth)']=lambda p,a,e,d,nw,al: a<=3*math.sqrt(math.log(p))*math.log(math.log(p))*2
H['H16 a_min = 3 or 7 for p QNR mod 7']=lambda p,a,e,d,nw,al: (leg(p%7,7)!=6) or a<=7
lim=int(sys.argv[2]) if len(sys.argv)>2 else len(rows)
for name,f in H.items():
    cex=None; n=0
    for (p,a,e,d,nw,al) in rows[:lim]:
        n+=1
        if not f(p,a,e,d,nw,al): cex=(p,a,e,d,nw,al); break
    print(('SURVIVES ' if cex is None else 'DEAD     ')+name+('' if cex is None else f'   first counterexample p={cex[0]} a_min={cex[1]} e={cex[2]} nwork={cex[4]}'))
c=Counter(a for (p,a,*_) in rows)
print('a_min frequencies:',sorted(c.items())[:20])
