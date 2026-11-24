# orbit representatives of incidence matrices (nr x nc, row-major strings) under row and column permutations restricted to rows/columns
# with EQUAL part dimensions.  usage: orbits.py ROWDIMS COLDIMS case1 case2 ...
import sys, itertools
rd=[int(c) for c in sys.argv[1]]; cd=[int(c) for c in sys.argv[2]]; nr,nc=len(rd),len(cd)
rp=[p for p in itertools.permutations(range(nr)) if all(rd[p[i]]==rd[i] for i in range(nr))]
cp=[q for q in itertools.permutations(range(nc)) if all(cd[q[m]]==cd[m] for m in range(nc))]
reps={}
for s in sys.argv[3:]:
    S=[[int(s[nc*i+m]) for m in range(nc)] for i in range(nr)]
    orb=min(''.join(str(S[p[i]][q[m]]) for i in range(nr) for m in range(nc)) for p in rp for q in cp)
    reps.setdefault(orb,[]).append(s)
for k,v in sorted(reps.items()): print(k,len(v))
