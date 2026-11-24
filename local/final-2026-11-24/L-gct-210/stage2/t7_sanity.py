# (a) exact check of the T2 cubic; (b) sanity of (T0) [3x2 zero block ZBF] on the exact examples (must not be contradicted)
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief')
from exactla import Fr, perm as eperm
import numpy as np
bad=0
for t,a1,a2,a3 in itertools.product(range(-2,3),repeat=4):
    M=[[t,a1,-t-a1],[t,-a2,t+a2],[t,-a3,t+a3]]; M=[[Fr(x) for x in r] for r in M]
    if eperm(M)!=2*t*(t*a1+a1*a2+a1*a3-a2*a3): bad+=1
G=np.array([[0,1,0,0],[1,0,1,1],[0,1,0,-1],[0,1,-1,0]])
print('T2 cubic identity violations on 5^4 grid:',bad,'  det of integer Gram matrix of the quadric:',round(np.linalg.det(G)))
from core import *
from testAB_lib import hat, sub_with_zero, rank
rng=np.random.default_rng(4)
tot=0; viol=0; stats={}
for name,f in SP.items():
    B=f(); Bh=hat(B)
    for rows in itertools.combinations(range(5),3):
        oth=[i for i in range(5) if i not in rows]
        for S in itertools.combinations(range(5),3):
            Sc=[c for c in range(5) if c not in S]
            U=sub_with_zero(Bh,[(i,j) for i in rows for j in Sc]); d=U.shape[1]
            if d==0: continue
            tot+=1; inL=np.abs(U[0,:]).max()<1e-9
            v3=[];v2=[];el=[]
            for _ in range(6):
                c=U@(rng.normal(size=d)+1j*rng.normal(size=d)); u=np.tensordot(c,Bh,1)
                v3.append(perm(u[np.ix_(rows,S)])); v2.append(perm(u[np.ix_(oth,Sc)])); el.append(c[0])
            v3=np.array(v3); v2=np.array(v2); el=np.array(el)
            if not inL:
                k3=v3[0]/el[0]**3; k2=v2[0]/el[0]**2
                ok=np.abs(v3-k3*el**3).max()<1e-7 and np.abs(v2-k2*el**2).max()<1e-7; typ='B1*'
            else:
                ok=(np.abs(v3).max()<1e-8) or (np.abs(v2).max()<1e-8); typ='inL'
            stats[(typ,ok)]=stats.get((typ,ok),0)+1
            if not ok: viol+=1
print('(T0) on examples',list(SP.keys()),': cases',tot,'violations',viol,stats)
