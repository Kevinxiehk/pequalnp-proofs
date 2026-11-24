# Theorem NC'-DC: dim L' = e + 3 + delta - s1 - s2 - s3 with delta = dim Q_dc, s1 = e^col(Q) - rank rho, s2 = 3 - e^col(Q) - x_n, s3 = e - rank kappa
import sys,glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np
from clm import *
from ext_chk import lines
CK=np.array([24,6,2,1,0,0.])[DEG]
def rk(M,tol=1e-5):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum()) if s.size else 0
def data(Z,n,e):
    d=Z.shape[0]; oth=[j for j in range(5) if j!=n]
    Zq=Z[:,:,oth]; u,s,vh=np.linalg.svd(Zq.reshape(d,-1),full_matrices=False); dQ=int((s>1e-5).sum()); Bq=vh[:dQ].reshape(dQ,4,4)
    rho=Bq.sum(2); kap=Bq.sum(1); r1=rk(rho); r2=rk(kap); delta=dQ-rk(np.concatenate([rho,kap],1))
    Zp=np.zeros((dQ,4,5),complex); Zp[:,:,oth]=Bq
    rng=np.random.default_rng(1); A=rng.normal(size=(80,dQ))+1j*rng.normal(size=(80,dQ)); A/=np.linalg.norm(A,axis=1)[:,None]
    X=np.einsum('nk,kab->nab',A,Zp); G,loo=G_and_loo(X); M=np.stack([(loo[i]*CK).sum(1) for i in range(4)],1); ecol=rk(M-24,1e-4)
    return d,e,dQ,d-dQ,ecol,r1,r2,delta
if __name__=='__main__':
    tab={}
    for pat in sys.argv[1:]:
        for f in sorted(glob.glob(pat)):
            Z=np.load(f); d=Z.shape[0]; lev,row,col,e=lines(Z)
            for n in range(5):
                if col[n]<1e-5:
                    d,e,dQ,xn,ecol,r1,r2,delta=data(Z,n,e); s1=ecol-r1; s2=3-ecol-xn; s3=e-r2
                    key=(d,e,dQ,xn,ecol,r1,r2,delta,s1,s2,s3,d==e+3+delta-s1-s2-s3); tab[key]=tab.get(key,0)+1
    print('(d,e | dimQ, x_n, e^col, rank rho, rank kappa | delta=dim Q_dc | s1,s2,s3 | identity holds): count')
    for k in sorted(tab): print('  ',k,':',tab[k])
