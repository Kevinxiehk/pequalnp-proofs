# numerical invariants of skew-deformed families (NOTES-reg2 15.4): builds the deformed basis exactly as defo_scan.py, evaluates at random
# complex parameters, reports (e, dim E_0, dim Omega, dim T_1, FO2).   usage: defo_inv.py FAMILY kind idx tgt [fixed params a=v ...]
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from famtool import *
fam,kind,idx,tgt=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4]); fixed=dict(a.split('=') for a in sys.argv[5:])
src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read(); sys.argv=['x',fam,'16','1','1']
exec(src[:src.index('F=Family(params,bfn,d)')])
P0=list(params); R0=Ring(P0+['t']); Bs=bfn(R0,R0.var)
def support(B):
    cells=[(i,j) for i in range(4) for j in range(5) if B[i][j]]; return set(i for i,j in cells), set(j for i,j in cells)
if kind=='col': grp=[k for k,B in enumerate(Bs) if support(B)[1]=={idx}]
else: grp=[k for k,B in enumerate(Bs) if support(B)[0]=={idx}]
assert len(grp)==2, grp
from nc_num import report
rg=np.random.default_rng(3)
def ev(q,vals):
    s=0
    for k,v in q.items():
        t=complex(v)
        for e,x in zip(k,vals): t*=x**e
        s+=t
    return s
for trial in range(3):
    vals=[complex(fixed[n]) if n in fixed else complex(rg.normal(),rg.normal()) for n in P0]+[complex(rg.normal(),rg.normal())]
    M=np.array([[[ev(B[i][j],vals) if B[i][j] else 0 for j in range(5)] for i in range(4)] for B in Bs])
    v=[M[g][:,idx] if kind=='col' else M[g][idx,:] for g in grp]
    G=np.array([[v[0]@v[0],v[0]@v[1]],[v[0]@v[1],v[1]@v[1]]]); J=[G[0,1]*v[0]-G[0,0]*v[1],G[1,1]*v[0]-G[0,1]*v[1]]
    for n,g in enumerate(grp):
        if kind=='col': M[g][:,tgt]+=vals[-1]*J[n]
        else: M[g][tgt,:]+=vals[-1]*J[n]
    report('%s %s %d->%d %s'%(fam,kind,idx,tgt,fixed),M)
