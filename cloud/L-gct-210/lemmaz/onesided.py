import numpy as np, sys; sys.path.insert(0,"/home/claude/work/L-gct-210/lemmaz")
from core import *
rng=np.random.default_rng(int(sys.argv[1])); n=int(sys.argv[2]); N=int(sys.argv[3])
def cc(x):
    c=x.reshape(n-1,n); return np.vstack([c,-c.sum(0)[None,:]])
for st in range(N):
    m=(n-1)*n
    lam=rng.normal(size=m)+1j*rng.normal(size=m)
    F=lambda x: np.concatenate([minors(cc(x)).ravel(),[lam@x-1]])
    x,r=solve(F,rng.normal(size=m)+1j*rng.normal(size=m))
    g=cc(x); g/=np.abs(g).max()
    rn=np.abs(g).max(1); cn=np.abs(g).max(0); sv=np.linalg.svd(g,compute_uv=False)
    print(st,"res %.1e"%r,"minrow %.1e mincol %.1e"%(rn.min(),cn.min()),"rank",int((sv>1e-6).sum()),"|rowsums| %.1e"%np.abs(g.sum(1)).max())
