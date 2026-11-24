# for every extremal example and every neutral column n: Q = L' minus column n (4x4 level), x_n, e^col(Q), e(Q)
import sys,glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np
from clm import *
from ext_chk import lines
def rk(M,tol=1e-5):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol*max(1,s[0])).sum()) if len(s) else 0
def qdata(Z,n,ns=80,seed=4):
    d=Z.shape[0]; Zq=Z.copy(); Zq[:,:,n]=0
    dQ=rk(Zq.reshape(d,-1),1e-5)
    rng=np.random.default_rng(seed); A=rng.normal(size=(ns,d))+1j*rng.normal(size=(ns,d)); A/=np.linalg.norm(A,axis=1)[:,None]
    X=np.einsum('nk,kab->nab',A,Zq); G,loo=G_and_loo(X)
    CK=np.array([24,6,2,1,0,0.])[DEG]
    M=np.stack([(loo[i]*CK).sum(1) for i in range(4)],1)          # (ns,4) row-deletion level polynomials of Q: sum_k (4-k)! P_k(q minus row i)
    lev4=np.abs(G[:,DEG==4].sum(1)-G[:,31^(1<<n)]).max()               # should be: perm(J+q)=24 -> coefficient check below
    ecol=rk(M-24,1e-5)
    # standard defect of Q (delete column j != n of Q: level polynomial of the 4x3 rest)
    cols=[j for j in range(5) if j!=n]
    R=np.stack([sum(CK[T]*G[:,T] for T in range(32) if DEG[T]<=3 and not (T>>j)&1 and not (T>>n)&1) for j in cols],1)
    eQ=rk(R-24,1e-5)
    return dQ,d-dQ,ecol,eQ,np.abs(M.sum(1)-96).max()
tab={}; ERR=[]
for pat in sys.argv[1:]:
    for f in sorted(glob.glob(pat)):
        Z=np.load(f); d=Z.shape[0]; lev,row,col,e=lines(Z)
        if d!=e+3: continue
        for n in range(5):
            if col[n]<1e-5:
                dQ,xn,ecol,eQ,err=qdata(Z,n); key=(d,e,dQ,xn,ecol,eQ); tab[key]=tab.get(key,0)+1; ERR.append(err)
print("(d, e | dim Q, x_n, e^col(Q), e(Q)) : count     [bounds: x_n <= 3 - e^col(Q);  conj dim Q <= e^col(Q)+3, dim Q <= e(Q)+3]")
for k in sorted(tab): print('  ',k,':',tab[k], '' if k[2]<=k[4]+3 and k[2]<=k[5]+3 and k[3]<=3-k[4] else '  <-- VIOLATION')
print('max |sum_i M_i - 96| =',max(ERR))
