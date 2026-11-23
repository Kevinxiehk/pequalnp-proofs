# verify column-centred formulas for P_k (n=5): rows t_i, G = t^T t, T_abc = sum_i t_ia t_ib t_ic
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/split')
from core import *
import itertools
rng=np.random.default_rng(3)
def esymv(v,k): return sum(np.prod([v[c] for c in C]) for C in itertools.combinations(range(5),k))
for trial in range(3):
    t=rnd((5,5),rng); t=t-t.mean(0,keepdims=True)   # column sums zero
    P=Pk(t[None])[0]
    G=t.T@t
    f2=-sum(esymv(t[i],2) for i in range(5))
    f3=2*sum(esymv(t[i],3) for i in range(5))
    pair4=sum(G[a,b]*G[c,d]+G[a,c]*G[b,d]+G[a,d]*G[b,c] for a,b,c,d in itertools.combinations(range(5),4))
    f4=-6*sum(esymv(t[i],4) for i in range(5))+pair4
    T3=lambda a,b,c: (t[:,a]*t[:,b]*t[:,c]).sum()
    f5=24*sum(esymv(t[i],5) for i in range(5))-2*sum(G[a,b]*T3(*[c for c in range(5) if c not in (a,b)]) for a,b in itertools.combinations(range(5),2))
    print(abs(P[2]-f2),abs(P[3]-f3),abs(P[4]-f4),abs(P[5]-f5))
