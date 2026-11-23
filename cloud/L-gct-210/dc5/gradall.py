import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/dc5')
import itertools, numpy as np
from graded import solve
def mul2(d):  # chi_k -> chi_{2k}
    n=[0]*4
    for k in range(1,5): n[(2*k)%5-1]=d[k-1]
    return tuple(n)
reps=[]; seen=set()
for d in itertools.product(range(int(sys.argv[4])+1),repeat=4):
    if sum(d)!=int(sys.argv[4]) or max(d)>4 or d in seen: continue
    orb={d}; x=d
    for _ in range(3): x=mul2(x); orb.add(x)
    seen|=orb; reps.append(d)
print(len(reps),'orbit reps')
ks=[int(c) for c in sys.argv[1]]
for d in reps:
    sols=solve(list(d),ks,int(sys.argv[2]),1,tl=float(sys.argv[3]))
    fs=sorted(s[0] for s in sols)
    print(d,'solved',sum(f<1e-9 for f in fs),'/',len(fs),'best %.1e'%fs[0],flush=True)
