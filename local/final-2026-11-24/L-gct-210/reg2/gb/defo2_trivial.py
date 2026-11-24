# Round 13: is the SECOND deformation trivial?  rank [M(t,0); M(t,t2)] = 6 <=> trivial.  usage: defo2_trivial.py FAMILY k1,i1,t1 k2,i2,t2 name=value ...
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
import numpy as np
from famtool import *
fam,d1,d2=sys.argv[1],sys.argv[2],sys.argv[3]; fixed=dict(a.split('=') for a in sys.argv[4:])
src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read(); sys.argv=['x',fam,'16','1','1']
exec(src[:src.index('F=Family(params,bfn,d)')])
P0=list(params); R0=Ring(P0); Bs=bfn(R0,R0.var)
def support(B):
    cells=[(i,j) for i in range(4) for j in range(5) if B[i][j]]; return set(i for i,j in cells), set(j for i,j in cells)
def ev(q,vals): return sum(complex(v)*np.prod([x**e for e,x in zip(k,vals)]) for k,v in q.items())
rg=np.random.default_rng(2); vals=[complex(fixed[n]) if n in fixed else complex(rg.normal(),rg.normal()) for n in P0]
M=np.array([[[ev(B[i][j],vals) if B[i][j] else 0 for j in range(5)] for i in range(4)] for B in Bs])
def apply(M,spec,t):
    kind,idx,tgt=spec.split(','); idx=int(idx); tgt=int(tgt); M=M.copy()
    grp=[k for k,B in enumerate(Bs) if (support(B)[1]=={idx} if kind=='col' else support(B)[0]=={idx})]
    v=[M[g][:,idx] if kind=='col' else M[g][idx,:] for g in grp]
    G=np.array([[v[0]@v[0],v[0]@v[1]],[v[0]@v[1],v[1]@v[1]]]); J=[G[0,1]*v[0]-G[0,0]*v[1],G[1,1]*v[0]-G[0,1]*v[1]]
    for n,g in enumerate(grp):
        if kind=='col': M[g][:,tgt]+=t*J[n]
        else: M[g][tgt,:]+=t*J[n]
    return M,abs(np.linalg.det(G))
M1,dg1=apply(M,d1,0.6+0.2j); M2,dg2=apply(M1,d2,-0.4+0.5j)
r1=np.linalg.matrix_rank(M1.reshape(len(M1),-1),tol=1e-9); r=np.linalg.matrix_rank(np.concatenate([M1,M2]).reshape(2*len(M1),-1),tol=1e-9)
print('%s %s + %s %s: det G2 = %.1e, dim M1 = %d, rank [M1;M2] = %d => second deformation %s'%(fam,d1,d2,fixed,dg2,r1,r,'TRIVIAL' if r==r1 else 'genuine'))
