# Round 14: numerics of a 3-dim-part deformation (defo_scan3 construction) at a point: level error, dim, triviality, (e,E0,Omega,T1,FO2).
#   usage: defo3_num.py FAMILY kind idx tgt s1,s2,s3 name=value ...
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, itertools
from famtool import *
fam,kind,idx,tgt=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4]); svec=np.array([complex(x) for x in sys.argv[5].split(',')]); fixed=dict(a.split('=') for a in sys.argv[6:])
src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read(); sys.argv=['x',fam,'16','1','1']
exec(src[:src.index('F=Family(params,bfn,d)')])
P0=list(params); R0=Ring(P0); Bs=bfn(R0,R0.var)
def support(B):
    cells=[(i,j) for i in range(4) for j in range(5) if B[i][j]]; return set(i for i,j in cells), set(j for i,j in cells)
def ev(q,vals): return sum(complex(v)*np.prod([x**e for e,x in zip(k,vals)]) for k,v in q.items())
rg=np.random.default_rng(5); vals=[complex(fixed[n]) if n in fixed else complex(rg.normal(),rg.normal()) for n in P0]
M=np.array([[[ev(B[i][j],vals) if B[i][j] else 0 for j in range(5)] for i in range(4)] for B in Bs])
g=[k for k,B in enumerate(Bs) if (support(B)[1]=={idx} if kind=='col' else support(B)[0]=={idx})]
vecs=np.array([M[k][:,idx] if kind=='col' else M[k][idx,:] for k in g])
trip=[g[t] for t in next(t for t in itertools.combinations(range(len(g)),3) if np.linalg.matrix_rank(vecs[list(t)],tol=1e-8)==3)]
drop=[k for k in g if k not in trip]
for k in drop: M[k]=0
v=np.array([M[k][:,idx] if kind=='col' else M[k][idx,:] for k in trip]); G=v@v.T
adj=np.array([[(-1)**(a+b)*np.linalg.det(np.delete(np.delete(G,b,0),a,1)) for b in range(3)] for a in range(3)])
s1,s2,s3=svec; S=np.array([[0,s3,-s2],[-s3,0,s1],[s2,-s1,0]]); Bm=adj@S
M0=M.copy()
for b,kk in enumerate(trip):
    img=sum(Bm[a,b]*v[a] for a in range(3))
    if kind=='col': M[kk][:,tgt]+=img
    else: M[kk][tgt,:]+=img
keep=[k for k in range(len(M)) if k not in drop]
r0=np.linalg.matrix_rank(M0[keep].reshape(len(keep),-1),tol=1e-9); r=np.linalg.matrix_rank(np.concatenate([M0[keep],M[keep]]).reshape(2*len(keep),-1),tol=1e-9)
print('%s %s %d->%d s=%s %s: rank B = %d, dim M0 = %d, rank [M0;M] = %d => %s'%(fam,kind,idx,tgt,sys.argv[5] if False else list(np.round(svec,3)),fixed,np.linalg.matrix_rank(Bm,tol=1e-9),r0,r,'TRIVIAL' if r==r0 else 'genuine'))
from nc_num import report
report('   invariants',M[keep])
import os
if os.environ.get('SAVE'): np.save(os.environ['SAVE'],M[keep]); print('saved',os.environ['SAVE'])
