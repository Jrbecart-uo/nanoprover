exec(open("e2e.py").read().split("fails=0")[0])
import statistics
for N in (300,900):
    finals=[]; maxes=[]; hsum=[]
    for sd in range(6):
        y,terms,G,E=run(N,1000+sd)
        finals.append(E[-1]); maxes.append(max(E))
    print(f"N={N}: final excess {finals}  max excess {maxes}")
