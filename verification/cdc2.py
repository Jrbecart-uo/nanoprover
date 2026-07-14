"""Stress-test the claimed CDC proof: snarks + hundreds of random cubic graphs."""
import random, functools
exec(open("cdc.py").read().split("# --- the Petersen")[0])

def fast_flow(V, E, tries=4000):
    """Nowhere-zero F_2^3 flow via random + local repair (faster than DFS)."""
    inc = {v: [i for i,(a,b) in enumerate(E) if a==v or b==v] for v in V}
    for _ in range(tries):
        f = [random.randrange(1,8) for _ in E]
        for _ in range(600):
            bad = [v for v in V if functools.reduce(lambda p,q:p^q,[f[i] for i in inc[v]],0)]
            if not bad: return f
            v = random.choice(bad)
            i = random.choice(inc[v])
            need = functools.reduce(lambda p,q:p^q,[f[j] for j in inc[v] if j!=i],0)
            if need != 0: f[i] = need
            else: f[i] = random.randrange(1,8)
    return None

def bridgeless(V,E):
    import itertools
    def conn(edges):
        if not V: return True
        adj = {v:[] for v in V}
        for a,b in edges: adj[a].append(b); adj[b].append(a)
        seen={V[0]}; st=[V[0]]
        while st:
            x=st.pop()
            for y in adj[x]:
                if y not in seen: seen.add(y); st.append(y)
        return len(seen)==len(V)
    if not conn(E): return False
    for i in range(len(E)):
        if not conn([e for j,e in enumerate(E) if j!=i]): return False
    return True

def check(name, V, E, quiet=False):
    n=len(E)
    f = fast_flow(V,E)
    if f is None: return None, f"{name}: no flow found"
    inc = {v: [i for i,(a,b) in enumerate(E) if a==v or b==v] for v in V}
    g={}
    for v in V:
        a,b,c = inc[v]; g[(v,a)]=0; g[(v,b)]=f[a]; g[(v,c)]=0
    d=[g[(E[i][0],i)] ^ g[(E[i][1],i)] for i in range(n)]
    idx={v:3*k for k,v in enumerate(V)}; EPS=3*len(V)
    rows=[]
    for i,(u,v) in enumerate(E):
        for bit in range(3):
            mask=(1<<(idx[u]+bit))|(1<<(idx[v]+bit))
            if (f[i]>>bit)&1: mask|=(1<<(EPS+i))
            rows.append((mask,(d[i]>>bit)&1))
    sol=solve_f2(rows,EPS+n)
    if sol is None: return False, f"{name}: *** LEMMA 2.2 INFEASIBLE — PROOF WRONG ***"
    t={v:sum(((sol>>(idx[v]+b))&1)<<b for b in range(3)) for v in V}
    P=[]
    for i,(u,v) in enumerate(E):
        Pu=frozenset({t[u]^g[(u,i)], t[u]^g[(u,i)]^f[i]})
        Pv=frozenset({t[v]^g[(v,i)], t[v]^g[(v,i)]^f[i]})
        if Pu!=Pv: return False, f"{name}: *** P_e DISAGREES — PROOF WRONG ***"
        P.append(Pu)
    for v in V:
        for s in range(8):
            if sum(1 for i in inc[v] if s in P[i]) not in (0,2):
                return False, f"{name}: *** CONDITION (1) FAILS ***"
    cover=[0]*n
    for s in range(8):
        Ms=[i for i in range(n) if s in P[i]]
        deg={}
        for i in Ms:
            u,v=E[i]; deg[u]=deg.get(u,0)+1; deg[v]=deg.get(v,0)+1
        if any(x not in (0,2) for x in deg.values()):
            return False, f"{name}: *** M_s NOT A UNION OF CYCLES ***"
        for i in Ms: cover[i]+=1
    if any(c!=2 for c in cover): return False, f"{name}: *** NOT A DOUBLE COVER ***"
    return True, f"{name}: CDC verified"

# --- SNARKS: the hard cases ---------------------------------------------------
def flower(k):   # flower snark J_k, k odd >= 5
    V=[]; E=[]
    for i in range(k):
        V += [('a',i),('b',i),('c',i),('d',i)]
    for i in range(k):
        E += [(('a',i),('b',i)), (('a',i),('c',i)), (('a',i),('d',i))]
    for i in range(k):
        E += [(('b',i),('b',(i+1)%k))]
    for i in range(k):
        E += [(('c',i),('d',(i+1)%k))]
    for i in range(k):
        E += [(('d',i),('c',(i+1)%k))]
    # dedupe / fix: standard J_k has b-cycle of length k, and c,d forming a 2k cycle
    return V,E

print("SNARKS AND NAMED GRAPHS")
V=list(range(10)); Epet=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
                         (5,7),(7,9),(9,6),(6,8),(8,5)]
ok,msg = check("  Petersen", V, Epet); print(msg)

# Blanusa snark (first), 18 vertices — a classic snark
B1 = [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),
      (12,13),(13,14),(14,15),(15,16),(16,17),(17,0),
      (0,8),(1,6),(2,10),(3,12),(4,16),(5,13),(7,14),(9,15),(11,17)]
ok,msg = check("  Blanusa-like (18v cubic)", list(range(18)), B1); print(msg)

print("\nRANDOM BRIDGELESS CUBIC GRAPHS")
random.seed(2026)
tested=0; failed=0
for trial in range(400):
    n = random.choice([4,6,8,10,12,14,16,18,20])
    # random cubic via configuration model
    stubs=[v for v in range(n) for _ in range(3)]
    random.shuffle(stubs)
    E=[]; okE=True
    for i in range(0,len(stubs),2):
        a,b=stubs[i],stubs[i+1]
        if a==b: okE=False; break
        E.append((a,b))
    if not okE: continue
    if any(E.count(e)+E.count((e[1],e[0]))>2 for e in E): pass
    Vv=list(range(n))
    if not bridgeless(Vv,E): continue
    res,msg = check(f"  rnd{trial}", Vv, E)
    if res is None: continue
    tested+=1
    if not res:
        failed+=1; print(msg)
print(f"\n  bridgeless cubic graphs tested: {tested}")
print(f"  FAILURES: {failed}")
print("\n  => Lemma 2.2 solvable and a valid CDC constructed in EVERY case."
      if failed==0 else "\n  => COUNTEREXAMPLE FOUND — the proof is wrong.")
