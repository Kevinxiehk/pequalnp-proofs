# numerical invariants (incl. Omega basis and the extra E_0 direction) of a doubly skew-deformed family at fixed base parameters
#   usage: num_double.py FAMILY kind,idx,tgt kind2,idx2,tgt2 [name=value ...]
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from famtool import *
fam,d1,d2=sys.argv[1],sys.argv[2],sys.argv[3]; fixed=dict(a.split('=') for a in sys.argv[4:])
src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read(); sys.argv=['x',fam,'16','1','1']
exec(src[:src.index('F=Family(params,bfn,d)')])
P0=list(params); R0=Ring(P0); Bs=bfn(R0,R0.var)
def support(B):
    cells=[(i,j) for i in range(4) for j in range(5) if B[i][j]]; return set(i for i,j in cells), set(j for i,j in cells)
def ev(q,vals):
    s=0
    for k,v in q.items():
        t=complex(v)
        for e,x in zip(k,vals): t*=x**e
        s+=t
    return s
from nc_num import report
from a5 import onb
from a6 import E0
rg=np.random.default_rng(4)
for trial in range(2):
    vals=[complex(fixed[n]) if n in fixed else complex(rg.normal(),rg.normal()) for n in P0]
    M=np.array([[[ev(B[i][j],vals) if B[i][j] else 0 for j in range(5)] for i in range(4)] for B in Bs])
    for dspec in [x for x in (d1,d2) if x!="none"]:
        kind,idx,tgt=dspec.split(','); idx=int(idx); tgt=int(tgt)
        grp=[k for k,B in enumerate(Bs) if (support(B)[1]=={idx} if kind=='col' else support(B)[0]=={idx})]
        v=[M[g][:,idx] if kind=='col' else M[g][idx,:] for g in grp]
        G=np.array([[v[0]@v[0],v[0]@v[1]],[v[0]@v[1],v[1]@v[1]]]); J=[G[0,1]*v[0]-G[0,0]*v[1],G[1,1]*v[0]-G[0,1]*v[1]]
        tt=complex(rg.normal(),rg.normal())
        for n,g in enumerate(grp):
            if kind=='col': M[g][:,tgt]+=tt*J[n]
            else: M[g][tgt,:]+=tt*J[n]
    report('%s %s + %s %s'%(fam,d1,d2,fixed),M)
    Bo=onb(M); E=E0(Bo,rg,npts=160); Q=E.reshape(len(E),20); found=[]
    for i in range(4):
        dd=np.full((4,5),-1.0); dd[i]=3; x=np.linalg.lstsq(Q.T,dd.ravel(),rcond=None)[0]
        if np.linalg.norm(Q.T@x-dd.ravel())<1e-8: found.append('row,%d'%i)
    for c in range(5):
        dd=np.full((4,5),-1.0); dd[:,c]=4; x=np.linalg.lstsq(Q.T,dd.ravel(),rcond=None)[0]
        if np.linalg.norm(Q.T@x-dd.ravel())<1e-8: found.append('col,%d'%c)
    print('   d candidates:',found)
