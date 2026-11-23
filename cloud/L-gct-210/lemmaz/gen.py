import numpy as np, sys; sys.path.insert(0,"/home/claude/work/L-gct-210/lemmaz")
from core import *
rng=np.random.default_rng(int(sys.argv[1])); n=int(sys.argv[2]); N=int(sys.argv[3])
def dc(x):
    c=x.reshape(n-1,n-1); g=np.zeros((n,n),complex); g[:n-1,:n-1]=c
    g[:n-1,n-1]=-c.sum(1); g[n-1,:]=-g[:n-1].sum(0); return g
# sanity: Kirkup generator formula
a=rng.normal(size=5)+1j*rng.normal(size=5); b=rng.normal(size=5)+1j*rng.normal(size=5)
D=np.outer(a,b)-np.outer(b,a); B=np.zeros((5,5),complex)
for m in range(5):
    for q in range(5):
        if m!=q: B[m,q]=1/np.prod([D[m,k]*D[q,k] for k in range(5) if k not in (m,q)])
print("Kirkup generator check |Ba|,|Bb|,|B|:",np.abs(B@a).max(),np.abs(B@b).max(),np.abs(B).max())
res=[]
for st in range(N):
    lam=rng.normal(size=(n-1)**2)+1j*rng.normal(size=(n-1)**2)
    F=lambda x: np.concatenate([minors(dc(x)).ravel(),[lam@x-1]])
    x0=rng.normal(size=(n-1)**2)+1j*rng.normal(size=(n-1)**2)
    x,r=solve(F,x0)
    g=dc(x); g/=np.abs(g).max()
    rn=np.abs(g).max(1); cn=np.abs(g).max(0); sv=np.linalg.svd(g,compute_uv=False)
    print(st,"res %.1e"%r,"minrow %.1e mincol %.1e"%(rn.min(),cn.min()),"zero rows/cols",int((rn<1e-6).sum()),int((cn<1e-6).sum()),"sv",np.round(sv,4))
