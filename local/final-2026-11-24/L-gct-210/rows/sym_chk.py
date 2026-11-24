# (SYM_5) test: for 5x5 level spaces L:  dim L <= e_row(L) + e_col(L) ?
#   e_row = dim span{ (N(J+t minus column j) - 120)_j }, e_col = dim span{ (N(J+t minus row i) - 120)_i }   (both <= 4)
import sys,glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np
from clm import *
CK=np.array([120,24,6,2,1,0.])[DEG]
def sv(M):
    s=np.linalg.svd(M,compute_uv=False); return s
def defects(B,ns=120,seed=11,tol=1e-4):
    d=B.shape[0]; rng=np.random.default_rng(seed)
    A=rng.normal(size=(ns,d))+1j*rng.normal(size=(ns,d)); A/=np.linalg.norm(A,axis=1)[:,None]
    X=np.einsum('nk,kab->nab',A,B); G,loo=G_and_loo(X)
    lev=np.abs(G@Rlevel(5).T).max()
    Nc=np.stack([(G*CK*(1-((np.arange(32)>>j)&1))).sum(1) for j in range(5)],1)      # delete column j
    Nr=np.stack([(loo[i]*CK).sum(1) for i in range(5)],1)                            # delete row i
    s1=sv(Nc-120); s2=sv(Nr-120)
    return lev,int((s1>tol).sum()),int((s2>tol).sum()),s1,s2,np.abs(Nc.sum(1)-600).max(),np.abs(Nr.sum(1)-600).max()
if __name__=='__main__':
    tab={}; bad=[]; n=0
    for pat in sys.argv[1:]:
        for f in sorted(glob.glob(pat)):
            try: B=np.load(f)
            except Exception: continue
            if B.ndim==2 and B.shape[1]==25: B=B.reshape(-1,5,5)
            if B.ndim!=3 or B.shape[1:]!=(5,5) or B.shape[0]<1: continue
            B=B.astype(complex); d0=B.shape[0]
            u,s,vh=np.linalg.svd(B.reshape(d0,-1),full_matrices=False); k=int((s>1e-6*s[0]).sum()); B=vh[:k].reshape(k,5,5)
            lev,er,ec,s1,s2,c1,c2=defects(B)
            if lev>1e-7: continue
            n+=1; key=(k,er,ec); tab[key]=tab.get(key,0)+1
            if k>er+ec: bad.append((f,k,er,ec,np.array2string(s1,precision=1),np.array2string(s2,precision=1)))
    print('level 5x5 spaces tested:',n)
    for k in sorted(tab): print('   (dim L, e_row, e_col) =',k,':',tab[k],'' if k[0]<=k[1]+k[2] else '   <-- dim > e_row + e_col')
    for b in bad[:12]: print('   VIOL',b)
