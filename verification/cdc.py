"""VERIFY OpenAI's claimed proof of the Cycle Double Cover conjecture.

The proof is CONSTRUCTIVE, so we can run it. Pipeline:
  1. find a nowhere-zero F_2^3 flow f  (8-flow theorem guarantees one)
  2. fix a local edge order at each vertex; set g(v,a)=0, g(v,b)=f(a), g(v,c)=0
  3. d_e = g(u,e) + g(v,e)
  4. SOLVE  t_u + t_v + eps_e * f(e) = d_e   over F_2   <- Lemma 2.2 says solvable
  5. P_e = { t_v + g(v,e),  t_v + g(v,e) + f(e) }
  6. M_s = { e : s in P_e } must be a disjoint union of cycles, for each s
  7. every edge must lie in exactly TWO of the M_s  => cycle double cover
If step 4 is ever infeasible, or step 6/7 fails, THE PROOF IS WRONG.
"""
import itertools, random

def flows(G, V, E):
    """nowhere-zero F_2^3 flow: XOR of incident edge labels = 0 at each vertex."""
    inc = {v: [i for i,(a,b) in enumerate(E) if a==v or b==v] for v in V}
    lab = [0]*len(E)
    def dfs(i):
        if i == len(E):
            return all(0 == (lambda vs: __import__('functools').reduce(lambda p,q:p^q, vs, 0))([lab[j] for j in inc[v]]) for v in V)
        for val in range(1, 8):
            lab[i] = val
            # prune: any vertex whose edges are all assigned must satisfy the flow law
            ok = True
            for v in V:
                es = inc[v]
                if all(j <= i for j in es):
                    x = 0
                    for j in es: x ^= lab[j]
                    if x != 0: ok = False; break
            if ok and dfs(i+1): return True
        lab[i] = 0
        return False
    return lab if dfs(0) else None

def solve_f2(rows, nvar):
    """Gaussian elimination over F_2. rows = list of (mask, rhs). Returns sol or None."""
    rows = [list(r) for r in rows]
    piv = {}
    for mask, rhs in rows:
        m, r = mask, rhs
        while m:
            b = m & -m
            if b in piv:
                pm, pr = piv[b]; m ^= pm; r ^= pr
            else:
                piv[b] = (m, r); break
        else:
            if r: return None           # 0 = 1  -> infeasible
    sol = 0
    for b in sorted(piv, reverse=True):
        m, r = piv[b]
        v = r
        mm = m ^ b
        while mm:
            lb = mm & -mm
            if sol & lb: v ^= 0   # bit contributions handled below
            mm ^= lb
        # back-substitute properly
        acc = r
        mm = m ^ b
        while mm:
            lb = mm & -mm
            if sol & lb: acc ^= 1
            mm ^= lb
        if acc: sol |= b
    return sol

def cdc(name, V, E):
    n = len(E)
    f = flows(V and V, V, E)
    if f is None: return f"{name}: no nowhere-zero F_2^3 flow found (!!)"
    inc = {v: [i for i,(a,b) in enumerate(E) if a==v or b==v] for v in V}
    # local order + gauge g[(v,e)]
    g = {}
    for v in V:
        a,b,c = inc[v]
        g[(v,a)] = 0; g[(v,b)] = f[a]; g[(v,c)] = 0
    d = [g[(E[i][0], i)] ^ g[(E[i][1], i)] for i in range(n)]
    # unknowns: t_v (3 bits each) then eps_e (1 bit each)
    idx = {v: 3*k for k,v in enumerate(V)}
    EPS = 3*len(V)
    rows = []
    for i,(u,v) in enumerate(E):
        for bit in range(3):
            mask = (1 << (idx[u]+bit)) | (1 << (idx[v]+bit))
            if (f[i] >> bit) & 1: mask |= (1 << (EPS+i))
            rows.append((mask, (d[i] >> bit) & 1))
    sol = solve_f2(rows, EPS + n)
    if sol is None:
        return f"{name}: *** LEMMA 2.2 FAILS — system infeasible. PROOF IS WRONG ***"
    t = {v: sum(((sol >> (idx[v]+b)) & 1) << b for b in range(3)) for v in V}
    eps = [(sol >> (EPS+i)) & 1 for i in range(n)]
    # check (4)
    for i,(u,v) in enumerate(E):
        if t[u] ^ t[v] ^ (f[i] if eps[i] else 0) != d[i]:
            return f"{name}: solution does not satisfy (4) — solver bug"
    # build P_e from EITHER endpoint; must agree
    P = []
    for i,(u,v) in enumerate(E):
        Pu = frozenset({t[u]^g[(u,i)], t[u]^g[(u,i)]^f[i]})
        Pv = frozenset({t[v]^g[(v,i)], t[v]^g[(v,i)]^f[i]})
        if Pu != Pv: return f"{name}: *** P_e DISAGREES ACROSS EDGE {i} — PROOF WRONG ***"
        if len(Pu) != 2: return f"{name}: P_e not a 2-set"
        P.append(Pu)
    # condition (1)
    for v in V:
        for s in range(8):
            c = sum(1 for i in inc[v] if s in P[i])
            if c not in (0,2):
                return f"{name}: *** CONDITION (1) FAILS at v={v}, s={s}: count {c} ***"
    # M_s are disjoint unions of cycles; each edge in exactly two
    cover = [0]*n
    cycles = 0
    for s in range(8):
        Ms = [i for i in range(n) if s in P[i]]
        deg = {}
        for i in Ms:
            u,v = E[i]; deg[u] = deg.get(u,0)+1; deg[v] = deg.get(v,0)+1
        if any(dd not in (0,2) for dd in deg.values()):
            return f"{name}: *** M_{s} is not a union of cycles ***"
        for i in Ms: cover[i] += 1
        cycles += 1 if Ms else 0
    if any(c != 2 for c in cover):
        return f"{name}: *** not a DOUBLE cover: edge multiplicities {set(cover)} ***"
    return f"{name}: CDC CONSTRUCTED AND VERIFIED  (|V|={len(V)}, |E|={n}, every edge covered exactly twice)"

# --- the Petersen graph: the canonical snark, where such arguments die -------
V = list(range(10))
E = [(0,1),(1,2),(2,3),(3,4),(4,0),
     (0,5),(1,6),(2,7),(3,8),(4,9),
     (5,7),(7,9),(9,6),(6,8),(8,5)]
print(cdc("PETERSEN", V, E))

# --- K4 and K_{3,3} (cubic, bridgeless) --------------------------------------
print(cdc("K4", [0,1,2,3], [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]))
print(cdc("K3,3", [0,1,2,3,4,5],
          [(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)]))
# --- the 3-cube ---------------------------------------------------------------
Q3 = [(0,1),(1,3),(3,2),(2,0),(4,5),(5,7),(7,6),(6,4),(0,4),(1,5),(2,6),(3,7)]
print(cdc("Q3 (cube)", list(range(8)), Q3))
