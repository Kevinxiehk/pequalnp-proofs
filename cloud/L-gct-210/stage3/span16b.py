import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/stage3")
import numpy as np, itertools
from span16 import span_dim
rng=np.random.default_rng(3)
# coincidence patterns per plane P_i: partition of its three partners into classes of proportional marked vectors
def patterns(i):
    ks=[k for k in range(4) if k!=i]
    yield 'distinct',[[ks[0]],[ks[1]],[ks[2]]]
    for a,b in itertools.combinations(range(3),2):
        c=[x for x in range(3) if x not in (a,b)][0]
        yield 'pair %d%d'%(ks[a],ks[b]),[[ks[a],ks[b]],[ks[c]]]
    yield 'all',[ks]
res={}
for combo in itertools.product(*[list(patterns(i)) for i in range(4)]):
    marks=[]
    for i,(name,classes) in enumerate(combo):
        d={}
        for cl in classes:
            v=rng.normal(size=2)
            for k in cl: d[k]=v*rng.normal()
        marks.append(d)
    r=span_dim(marks)
    if r<16: res[tuple(c[0] for c in combo)]=r
print('patterns with span < 16:',len(res),'of 625')
# summarise: is span<16 iff some plane has all three proportional?
bad=[k for k in res if 'all' not in k]
print('deficient patterns WITHOUT an all-proportional plane:',len(bad))
for k in bad[:40]: print('  ',k,res[k])
full_with_all=[1 for combo in itertools.product(*[[p[0] for p in patterns(i)] for i in range(4)]) if 'all' in combo and combo not in res]
print('patterns WITH an all-proportional plane but full span:',len(full_with_all))
