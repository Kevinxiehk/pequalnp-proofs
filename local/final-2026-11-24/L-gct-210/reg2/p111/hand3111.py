# Round 12: (3,1,1,1|) (single class; TIMEOUT in the pool) reduced by hand exactly as (3,1,1|1)-101: U_1, U_2, U_3 lie in the line
# U_0^perp cap 1^perp = C n, pairwise orthogonal => n isotropic, n in U_0, U_0 = n^perp cap 1^perp.  M = e_0 (x) (n^perp cap 1^perp) (+) e_1 n
# (+) e_2 n (+) e_3 n.  Test: level equations in n (spanning set of cross products) + sum n = 0 + <n,n> = 0, saturated by n.
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
params=['n0','n1','n2','n3','n4']
def bfn(R,V):
    n=[V(p) for p in params]; Bs=[]
    for a,b,c in itertools.combinations(range(5),3):
        Z=[[{} for _ in range(5)] for _ in range(4)]
        Z[0][a]=add(n[b],n[c],-1); Z[0][b]=add(n[c],n[a],-1); Z[0][c]=add(n[a],n[b],-1); Bs.append(Z)
    for i in (1,2,3):
        Z=[[{} for _ in range(5)] for _ in range(4)]; Z[i]=list(n); Bs.append(Z)
    return Bs
F=Family(params,bfn,13); np_=len(params)
lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
lines=[to_str_Q(q,params) for q in lev]+['n0+n1+n2+n3+n4','n0^2+n1^2+n2^2+n3^2+n4^2']
body='LIB "elim.lib";\nring R=0,(n0,n1,n2,n3,n4),dp;\nideal I=%s;\nI=std(I);\nI=sat(I,ideal(n0,n1,n2,n3,n4));\nI=std(I);\nprint("after sat: dim "+string(dim(I))+"  G[1] = "+string(I[1]));\nquit;\n'%(',\n'.join(lines))
open('/home/kevxhk/work/L-gct-210/reg2/p111/hand3111.sing','w').write(body); print('level equations:',len(lev))
