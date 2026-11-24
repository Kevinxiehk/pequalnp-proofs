# Round 13: is a deformation found by defo_scan_span TRIVIAL (M(t) = M(0))?  Numerical test at points of the locus: rank [M(0); M(t)] = 6 <=> trivial.
#   usage: defo_trivial.py FAMILY kind idx tgt name=value ...   (FAMILY = a basis version *_b)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
import numpy as np
from famtool import *
fam,kind,idx,tgt=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4]); fixed=dict(a.split('=') for a in sys.argv[5:])
src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read(); sys.argv=['x',fam,'16','1','1']
exec(src[:src.index('F=Family(params,bfn,d)')])
P0=list(params); R0=Ring(P0); Bs=bfn(R0,R0.var)
def support(B):
    cells=[(i,j) for i in range(4) for j in range(5) if B[i][j]]; return set(i for i,j in cells), set(j for i,j in cells)
def ev(q,vals): return sum(complex(v)*np.prod([x**e for e,x in zip(k,vals)]) for k,v in q.items())
rg=np.random.default_rng(1)
vals=[complex(fixed[n]) if n in fixed else complex(rg.normal(),rg.normal()) for n in P0]
M0=np.array([[[ev(B[i][j],vals) if B[i][j] else 0 for j in range(5)] for i in range(4)] for B in Bs])
grp=[k for k,B in enumerate(Bs) if (support(B)[1]=={idx} if kind=='col' else support(B)[0]=={idx})]
v=[M0[g][:,idx] if kind=='col' else M0[g][idx,:] for g in grp]
G=np.array([[v[0]@v[0],v[0]@v[1]],[v[0]@v[1],v[1]@v[1]]]); J=[G[0,1]*v[0]-G[0,0]*v[1],G[1,1]*v[0]-G[0,1]*v[1]]
Mt=M0.copy(); t=0.7-0.3j
for n,g in enumerate(grp):
    if kind=='col': Mt[g][:,tgt]+=t*J[n]
    else: Mt[g][tgt,:]+=t*J[n]
r0=np.linalg.matrix_rank(M0.reshape(len(M0),-1),tol=1e-9); r=np.linalg.matrix_rank(np.concatenate([M0,Mt]).reshape(2*len(M0),-1),tol=1e-9)
print('%s %s %d->%d %s: det G = %.2e, dim M0 = %d, rank [M0;Mt] = %d  => %s'%(fam,kind,idx,tgt,fixed,abs(np.linalg.det(G)),r0,r,'TRIVIAL' if r==r0 else 'genuine'))
