# Round 12: (3,1,1|1), incidence class 101 (TIMEOUT / out of memory in the pool) -- reduced by hand: the column element x vanishes at rows 0, 2,
# so x ~ (0,1,0,-1); u_1 vanishes at column 0; U_1, U_2 are orthogonal to the 3-dim U_0 inside 1^perp, so both lie in the line
# U_0^perp cap 1^perp = C n, and u_1 perp u_2 makes n isotropic, hence n in U_0 and U_0 = n^perp cap 1^perp, with n_0 = 0.
# So M = e_0 (x) (n^perp cap 1^perp)  (+)  e_1 n  (+)  e_2 n  (+)  (0,1,0,-1) e_0^T.  Test: level equations in n (spanning set) + n != 0.
import sys, subprocess; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
params=['n1','n2','n3','n4']
def bfn(R,V):
    c=R.const; n=[{}]+[V(p) for p in params]; Bs=[]
    for a in range(1,5):
        for b in range(a+1,5):
            Z=[[{} for _ in range(5)] for _ in range(4)]
            Z[0][a]=n[b]; Z[0][b]=scal(n[a],-1); Z[0][0]=add(n[a],n[b],-1); Bs.append(Z)
    for i in (1,2):
        Z=[[{} for _ in range(5)] for _ in range(4)]; Z[i]=list(n); Bs.append(Z)
    Z=[[{} for _ in range(5)] for _ in range(4)]; Z[1][0]=c(1); Z[3][0]=c(-1); Bs.append(Z)
    return Bs
F=Family(params,bfn,9); np_=len(params)
lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
lines=[to_str_Q(q,params) for q in lev]+['n1+n2+n3+n4','n1^2+n2^2+n3^2+n4^2']
body='LIB "elim.lib";\nring R=0,(n1,n2,n3,n4),dp;\nideal I=%s;\nI=std(I);\nI=sat(I,ideal(n1,n2,n3,n4));\nI=std(I);\nprint("after sat: dim "+string(dim(I))+"  G[1] = "+string(I[1]));\nquit;\n'%(',\n'.join(lines))
open('/home/kevxhk/work/L-gct-210/reg2/p111/hand311_101.sing','w').write(body)
print('level equations:',len(lev))
