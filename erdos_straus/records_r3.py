"""Anatomy of the record primes: why does every a < a_min fail?"""
from math import gcd
from collections import Counter
from model_r3 import pf, works
def subgroup(gens,a):
    S={1}; fr=[1]
    while fr:
        s=fr.pop()
        for g in gens:
            t=s*g%a
            if t not in S: S.add(t); fr.append(t)
    return S
def lqnr(p):
    q=2
    while pow(q,(p-1)//2,p)==1: q+=1
    return q
recs=[(73,7),(1129,11),(1201,23),(21169,31),(118801,59),(8803369,107)]
for p,am in recs:
    kinds=Counter(); prime_x=0
    for a in range(3,am,4):
        x=(p+a)//4
        f=pf(x)
        if len(f)==1: prime_x+=1
        gens=[q%a for q in set(f+[p]) if gcd(q,a)==1]
        kinds['subgroup (-1 unreachable)' if (a-1) not in subgroup(gens,a) else 'exponent cap']+=1
    print(f'p={p} a_min={am} least QNR={lqnr(p)} p mod 840={p%840}  failures: {dict(kinds)}  x_a prime for {prime_x}/{(am-3)//4} a')
