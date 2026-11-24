# do the 4x4 level spaces Q (L' minus neutral column) of the extremal examples have a deletable line again?  (triple towers)
import sys,glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np
from clm import *
from ext_chk import lines
def levpoly_err(X):
    """X: (N,p,5) matrices with some zero columns/rows removed logically; returns max |deg>=1 part of N(J+X)| for p x q' (q' = nonzero cols) -- generic weights"""
    return None
def lev_rect(B,ncols,ns=50,seed=3):
    # B: (d,p,5) with only `ncols` live columns (others zero). level polynomial of p x ncols matrix J+X: sum_k w_k P_k, w_k = (m-k)!/(m-min)!...; level <=> P_k = 0 (k>=1)
    d,p,_=B.shape; rng=np.random.default_rng(seed); A=rng.normal(size=(ns,d))+1j*rng.normal(size=(ns,d)); A/=np.linalg.norm(A,axis=1)[:,None]
    X=np.einsum('nk,kab->nab',A,B); G,_=G_and_loo(X); m=min(p,ncols)
    return max(np.abs(G[:,DEG==k].sum(1)).max() for k in range(1,m+1))
tab={}
for pat in sys.argv[1:]:
    for f in sorted(glob.glob(pat)):
        Z=np.load(f); d=Z.shape[0]; lev,row,col,e=lines(Z)
        if d!=e+3: continue
        for n in range(5):
            if col[n]>1e-5: continue
            oth=[j for j in range(5) if j!=n]; Zq=Z.copy(); Zq[:,:,n]=0
            u,s,vh=np.linalg.svd(Zq.reshape(d,-1),full_matrices=False); dQ=int((s>1e-5).sum()); Bq=vh[:dQ].reshape(dQ,4,5)
            dr=[]; dc=[]
            for i in range(4):
                B=np.delete(Bq,i,axis=1)                      # 3 x 4 live
                if lev_rect(B,4)<1e-5: dr.append(i)
            for j in oth:
                B=Bq.copy(); B[:,:,j]=0                        # 4 x 3 live
                if lev_rect(B,3)<1e-5: dc.append(j)
            key=(d,e,dQ,len(dr),len(dc)); tab[key]=tab.get(key,0)+1
print('(d,e,dim Q,#deletable rows of Q,#deletable columns of Q): count')
for k in sorted(tab): print('  ',k,':',tab[k])
