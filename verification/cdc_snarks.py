"""ADVERSARIAL TEST: run the construction on REAL SNARKS.

Snarks = bridgeless cubic graphs with NO nowhere-zero 4-flow (not 3-edge-
colourable). They are EXACTLY the graphs where the classical '4-flow => CDC'
argument fails, i.e. exactly where CDC was open. If the construction breaks
anywhere, it breaks here."""
import random, functools
exec(open("cdc.py").read().split("# --- the Petersen")[0])

def fast_flow(V, E, tries=6000):
    inc = {v: [i for i,(a,b) in enumerate(E) if a==v or b==v] for v in V}
    for _ in range(tries):
        f = [random.randrange(1,8) for _ in E]
        for _ in range(900):
            bad = [v for v in V if functools.reduce(lambda p,q:p^q,[f[i] for i in inc[v]],0)]
            if not bad: return f
            v = random.choice(bad); i = random.choice(inc[v])
            need = functools.reduce(lambda p,q:p^q,[f[j] for j in inc[v] if j!=i],0)
            f[i] = need if need != 0 else random.randrange(1,8)
    return None

def has4flow(V, E, tries=200000):
    """nowhere-zero F_2^2 flow? (randomised + repair; None-ish evidence only)"""
    inc = {v: [i for i,(a,b) in enumerate(E) if a==v or b==v] for v in V}
    for _ in range(tries//100):
        f = [random.randrange(1,4) for _ in E]
        for _ in range(300):
            bad = [v for v in V if functools.reduce(lambda p,q:p^q,[f[i] for i in inc[v]],0)]
            if not bad: return True
            v = random.choice(bad); i = random.choice(inc[v])
            need = functools.reduce(lambda p,q:p^q,[f[j] for j in inc[v] if j!=i],0)
            if need in (1,2,3): f[i] = need
            else: f[i] = random.randrange(1,4)
    return False

def run(name, V, E, rounds=200):
    n = len(E)
    inc = {v: [i for i,(a,b) in enumerate(E) if a==v or b==v] for v in V}
    assert all(len(inc[v]) == 3 for v in V), f"{name} not cubic!"
    res = {}
    for _ in range(rounds):
        f = fast_flow(V, E)
        if f is None:
            res["NO FLOW"] = res.get("NO FLOW",0)+1; continue
        orders = {v: random.sample(inc[v], 3) for v in V}
        g = {}
        for v in V:
            a,b,c = orders[v]; g[(v,a)]=0; g[(v,b)]=f[a]; g[(v,c)]=0
        d = [g[(E[i][0],i)] ^ g[(E[i][1],i)] for i in range(n)]
        idx = {v: 3*k for k,v in enumerate(V)}; EPS = 3*len(V)
        rows=[]
        for i,(u,v) in enumerate(E):
            for bit in range(3):
                mask = (1<<(idx[u]+bit))|(1<<(idx[v]+bit))
                if (f[i]>>bit)&1: mask |= (1<<(EPS+i))
                rows.append((mask,(d[i]>>bit)&1))
        sol = solve_f2(rows, EPS+n)
        if sol is None:
            res["*** LEMMA 2.2 INFEASIBLE ***"] = res.get("*** LEMMA 2.2 INFEASIBLE ***",0)+1
            continue
        t = {v: sum(((sol>>(idx[v]+b))&1)<<b for b in range(3)) for v in V}
        P=[]
        bad=False
        for i,(u,v) in enumerate(E):
            Pu=frozenset({t[u]^g[(u,i)], t[u]^g[(u,i)]^f[i]})
            Pv=frozenset({t[v]^g[(v,i)], t[v]^g[(v,i)]^f[i]})
            if Pu!=Pv: res["P DISAGREE"]=res.get("P DISAGREE",0)+1; bad=True; break
            P.append(Pu)
        if bad: continue
        for v in V:
            for s in range(8):
                if sum(1 for i in inc[v] if s in P[i]) not in (0,2):
                    res["COND(1) FAIL"]=res.get("COND(1) FAIL",0)+1; bad=True; break
            if bad: break
        if bad: continue
        cover=[0]*n
        for s in range(8):
            Ms=[i for i in range(n) if s in P[i]]
            deg={}
            for i in Ms:
                u,v=E[i]; deg[u]=deg.get(u,0)+1; deg[v]=deg.get(v,0)+1
            if any(x not in (0,2) for x in deg.values()):
                res["M_s NOT CYCLES"]=res.get("M_s NOT CYCLES",0)+1; bad=True; break
            for i in Ms: cover[i]+=1
        if bad: continue
        if any(c!=2 for c in cover):
            res["NOT DOUBLE COVER"]=res.get("NOT DOUBLE COVER",0)+1; continue
        res["CDC OK"]=res.get("CDC OK",0)+1
    return res

def flower(k):
    """Flower snark J_k, k odd >= 5. 4k vertices, 6k edges."""
    A=lambda i:('A',i%k); B=lambda i:('B',i%k); C=lambda i:('C',i%k); D=lambda i:('D',i%k)
    V=[X(i) for i in range(k) for X in (A,B,C,D)]
    E=[]
    for i in range(k):
        E += [(B(i),A(i)), (B(i),C(i)), (B(i),D(i))]     # the star at B_i
    for i in range(k):
        E += [(A(i), A(i+1))]                             # n-cycle on the A's
    for i in range(k-1):
        E += [(C(i), C(i+1))]                             # C_0..C_{k-1}
    E += [(C(k-1), D(0))]                                 # ...then into the D's
    for i in range(k-1):
        E += [(D(i), D(i+1))]
    E += [(D(k-1), C(0))]                                 # close the 2k-cycle
    return V, E

random.seed(2026)
print("REAL SNARKS — the graphs with NO 4-flow, exactly where CDC was open\n")
V,E = flower(5)
print(f"  Flower snark J5:  {len(V)} vertices, {len(E)} edges")
print(f"    has nowhere-zero 4-flow?  {has4flow(V,E)}   (False => genuine snark)")
print(f"    construction: {run('J5', V, E)}")

V,E = flower(7)
print(f"\n  Flower snark J7:  {len(V)} vertices, {len(E)} edges")
print(f"    has nowhere-zero 4-flow?  {has4flow(V,E)}")
print(f"    construction: {run('J7', V, E, rounds=100)}")

V,E = flower(9)
print(f"\n  Flower snark J9:  {len(V)} vertices, {len(E)} edges")
print(f"    construction: {run('J9', V, E, rounds=60)}")
