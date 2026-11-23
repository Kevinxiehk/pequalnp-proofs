import numpy as np, sys; sys.path.insert(0,"/home/claude/work/L-gct-210/lemmaz")
from core import *
rng=np.random.default_rng(1)
w=np.exp(2j*np.pi/5)
# twisted circulants g_ij = w^{k i} a_{j-i}; DC: sum a = 0, sum w^{-k d} a_d = 0 (k != 0)
for k in range(5):
    cons=[np.ones(5)]
    if k: cons.append(w**(-k*np.arange(5)))
    C=np.array(cons); 
    _,_,Vh=np.linalg.svd(C); N=Vh[len(cons):].conj().T   # null basis
    best=[]
    for st in range(30):
        lam=rng.normal(size=5)+1j*rng.normal(size=5)
        def F(x):
            a=N@x; g=np.array([[w**(k*i)*a[(j-i)%5] for j in range(5)] for i in range(5)])
            m=minors(g)
            return np.concatenate([m[0], [lam@a-1]])
        x0=rng.normal(size=N.shape[1])+1j*rng.normal(size=N.shape[1])
        x,res=solve(F,x0); best.append((res,np.linalg.norm(N@x)))
    best.sort(); print(k,N.shape[1],best[:4])
