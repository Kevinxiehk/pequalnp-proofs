import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
import numpy as np, itertools, glob
from t import *
from r5_FO2 import FO2
def Phi(x):
    return np.array([perm(np.delete(x,j,axis=1)) for j in range(x.shape[1])])
def pk(x,k):
    # p_k(Y)_j = P_k(Y minus column j)
    p,q=x.shape; out=[]
    for j in range(q):
        y=np.delete(x,j,axis=1); s=0
        for R in itertools.combinations(range(p),k):
            for C in itertools.combinations(range(q-1),k):
                s+=perm(y[np.ix_(R,C)])
        out.append(s)
    return np.array(out)
def phirank(B,n=40,seed=1):
    rng=np.random.default_rng(seed); d=len(B); V=[]
    for _ in range(n):
        c=rng.normal(size=d)+1j*rng.normal(size=d); V.append(Phi(np.einsum('k,kab->ab',c,B)))
    V=np.array(V); s=np.linalg.svd(V,compute_uv=False); return s
def defect(B,n=40,seed=2):
    rng=np.random.default_rng(seed); d=len(B); V=[]
    for _ in range(n):
        c=rng.normal(size=d)+1j*rng.normal(size=d); Y=np.einsum('k,kab->ab',c,B)
        for k in range(1,5): V.append(pk(Y,k))
    V=np.array(V); s=np.linalg.svd(V,compute_uv=False); return s
def embed(B,r=4):
    d=len(B); out=np.zeros((d,5,5),complex); rows=[i for i in range(5) if i!=r]; out[:,rows,:]=B; return out
if __name__=='__main__':
    rg=np.random.default_rng(5)
    for f in sys.argv[1:]:
        B=np.load(f); print(f, 'dim',len(B))
        print('  Phi sv',np.array2string(phirank(B),precision=2))
        print('  defect sv',np.array2string(defect(B),precision=2))
        n,rho,bd=FO2(embed(B),rg); print('  T1 dim',n,'rank',rho,'FO2 bound',bd)
