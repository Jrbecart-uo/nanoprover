import random, sys, math
p=int(sys.argv[1]); L=int(sys.argv[2]); W=int(sys.argv[3]); K=int(sys.argv[4]); trials=int(sys.argv[5])
MOD=1<<(L+64); pinv=pow(p,-1,MOD); U=[pow(pinv,g,MOD) for g in range(0,int(L*0.5)+K+5)]
mu=math.log(2)/math.log(p)
rates=[]
for t in range(trials):
    y=random.getrandbits(L)
    # state: (gamma_last, residual)  residual has bits < b cleared; process bit b
    beam=[(-1,y)]
    for b in range(L):
        nb={}
        for g,r in beam:
            if (r>>b)&1==0:
                key=(g,r); nb[key]=1
            else:
                for d in range(1,K+1):
                    g2=g+d; r2=(r-(U[g2]<<b))%MOD
                    nb[(g2,r2)]=1
        # prune: keep W states with smallest gamma, tie-break by longer zero run ahead
        items=list(nb.keys())
        if len(items)>W:
            def score(it):
                g,r=it; rr=r>>(b+1); z=((rr & -rr).bit_length()-1) if rr else 64
                return g - mu*min(z,20)
            items.sort(key=score); items=items[:W]
        beam=items
    best=min(g for g,r in beam)+1
    rates.append(best/L)
print(f"p={p} L={L} W={W} K={K}: gamma-rate mean {sum(rates)/len(rates):.4f} min {min(rates):.4f} max {max(rates):.4f}  (mu={mu:.4f})")
