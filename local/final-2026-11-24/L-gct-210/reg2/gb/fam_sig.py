# Round 14: line signature of a deformed family at a random parameter point: single-row dims, single-column dims, genuine pieces.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from famtool import *
fam,kind,idx,tgt=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4])
src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read(); sys.argv=['x',fam,'16','1','1']
exec(src[:src.index('F=Family(params,bfn,d)')])
P0=list(params); R0=Ring(P0); Bs=bfn(R0,R0.var)
def support(B):
    cells=[(i,j) for i in range(4) for j in range(5) if B[i][j]]; return set(i for i,j in cells), set(j for i,j in cells)
def ev(q,vals): return sum(complex(v)*np.prod([x**e for e,x in zip(k,vals)]) for k,v in q.items())
def build(vals,t):
    M=np.array([[[ev(B[i][j],vals) if B[i][j] else 0 for j in range(5)] for i in range(4)] for B in Bs])
    if kind=='none': return M
    grp=[k for k,B in enumerate(Bs) if (support(B)[1]=={idx} if kind=='col' else support(B)[0]=={idx})]
    v=[M[g][:,idx] if kind=='col' else M[g][idx,:] for g in grp]
    G=np.array([[v[0]@v[0],v[0]@v[1]],[v[0]@v[1],v[1]@v[1]]]); J=[G[0,1]*v[0]-G[0,0]*v[1],G[1,1]*v[0]-G[0,1]*v[1]]
    for n,g in enumerate(grp):
        if kind=='col': M[g][:,tgt]+=t*J[n]
        else: M[g][tgt,:]+=t*J[n]
    return M
if __name__=='__main__':
    rg=np.random.default_rng(3); vals=[complex(rg.normal(),rg.normal()) for _ in P0]; M=build(vals,0.7-0.2j)
    u,s,vh=np.linalg.svd(M.reshape(len(M),-1)); M=vh[:int((s>1e-9*s[0]).sum())].reshape(-1,4,5)
    from pieces import sub_supported
    a=[len(sub_supported(M,np.eye(4,dtype=bool)[i][:,None].repeat(5,1))) for i in range(4)]
    b=[len(sub_supported(M,np.eye(5,dtype=bool)[c][None,:].repeat(4,0))) for c in range(5)]
    print(fam,kind,idx,'->',tgt,': dim',len(M),' single-row',a,' single-col',b)
