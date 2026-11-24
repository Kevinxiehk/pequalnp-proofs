import numpy as np, sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/lemmaz")
from core import *
np.set_printoptions(precision=3,suppress=True,linewidth=200)
rng=np.random.default_rng(11)
# 4x5 DC matrices (row 5 zero) with five 4x4 subperms zero: param 3x4 core
def dc45(x):
    c=x.reshape(3,4); g=np.zeros((5,5),complex); g[:3,:4]=c; g[:3,4]=-c.sum(1); g[3,:]=-g[:3].sum(0); return g
cnt=0
for st in range(12):
    lam=rng.normal(size=(7,12))+1j*rng.normal(size=(7,12)); rhs=rng.normal(size=7)+1j*rng.normal(size=7)
    F=lambda x: np.concatenate([minors(dc45(x))[4],lam@x-rhs])
    x,r=solve(F,rng.normal(size=12)+1j*rng.normal(size=12))
    g=dc45(x)[:4]; g/=np.abs(g).max()
    rn=np.abs(g).max(1); cn=np.abs(g).max(0)
    # proportional rows / columns?
    def prop(V):
        out=[]
        for a in range(len(V)):
            for b in range(a+1,len(V)):
                s=np.linalg.svd(np.array([V[a],V[b]]),compute_uv=False)
                if s[1]<1e-6*s[0]: out.append((a,b))
        return out
    P3=[abs(perm(g[np.ix_(R,C)])) for R in __import__('itertools').combinations(range(4),3) for C in __import__('itertools').combinations(range(5),3)]
    print(st,"res %.0e"%r,"minrow %.0e mincol %.0e"%(rn.min(),cn.min()),"prop rows",prop(g),"prop cols",prop(g.T),"#zero entries",int((np.abs(g)<1e-7).sum()),"#zero 3x3 perms",int((np.array(P3)<1e-7).sum()),"rank",int((np.linalg.svd(g,compute_uv=False)>1e-7).sum()))
    if cnt<2 and rn.min()>1e-3 and cn.min()>1e-3: print(g); cnt+=1
