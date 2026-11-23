import numpy as np, sys; sys.path.insert(0,"/home/claude/work/L-gct-210/lemmaz")
from core import *
np.set_printoptions(precision=2,linewidth=200)
rng=np.random.default_rng(1)
def dc45(x):
    c=x.reshape(3,4); g=np.zeros((5,5),complex); g[:3,:4]=c; g[:3,4]=-c.sum(1); g[3,:]=-g[:3].sum(0); return g
ts=[0.0,1.0,-1.0,2.0,-0.5]
for st in range(16):
    l1=rng.normal(size=12)+1j*rng.normal(size=12); l2=rng.normal(size=12)+1j*rng.normal(size=12)
    def F(x):
        a=dc45(x[:12]); b=dc45(x[12:])
        out=[minors(a+t*b)[4] for t in ts]
        out.append(np.array([np.sum(a*a),np.sum(a*b),np.sum(b*b),np.sum(a**3),np.sum(a*a*b),np.sum(a*b*b),np.sum(b**3),
                             l1@x[:12]-1,l1@x[12:],l2@x[:12],l2@x[12:]-1]))
        return np.concatenate(out)
    x0=rng.normal(size=24)+1j*rng.normal(size=24)
    if st not in (6,15): 
        continue
    x,r=solve(F,x0,nfev=1200)
    x,r=solve(F,x,nfev=2500)
    a=dc45(x[:12]); b=dc45(x[12:]); sc=max(np.abs(a).max(),np.abs(b).max())
    print("run",st,"res %.1e"%r,"scale %.2f"%sc)
    print(" row maxima (rows 0-3) over plane:",np.maximum(np.abs(a[:4]).max(1),np.abs(b[:4]).max(1))/sc)
    print(" col maxima over plane:",np.maximum(np.abs(a).max(0),np.abs(b).max(0))/sc)
    print(" sv a:",np.linalg.svd(a,compute_uv=False)/sc," sv b:",np.linalg.svd(b,compute_uv=False)/sc)
    print(" sv of stacked plane basis (24-vector pairs):",np.linalg.svd(np.array([a.ravel(),b.ravel()]),compute_uv=False)/sc)
    np.save("plane_run%d.npy"%st,np.array([a,b]))
