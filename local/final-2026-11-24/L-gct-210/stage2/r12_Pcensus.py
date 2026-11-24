# Census of z = 3 candidates X = P (+) e_4 (x) Z [NOTES-stage2 R12-2]: P a 2-dim space of matrices supported on block rows 0,1,2 (rows 1..3 of L),
# Z a fixed random 3-dim subspace of 1^perp in C^5 placed in block row 3 (row 4 of L). Conditions: perm(J + xi) = 120 and the five 4x4
# column-deletion permanents G_j(xi) = 0 on X (Q-r (i),(ii)). LM from random starts; every hit re-verified on fresh points; then
# report the support pattern of P, single-column parts, dim T_1, Omega, FO2 and FO2-joint (LM).
import sys, itertools, numpy as np
from scipy.optimize import least_squares
A_=list(sys.argv); sys.argv=[A_[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r8_caseB.py').read().split("if __name__=='__main__':")[0])
SEED=int(A_[1]) if len(A_)>1 else 1; NTR=int(A_[2]) if len(A_)>2 else 10
rg=np.random.default_rng(SEED)
Z=rg.normal(size=(3,5))+1j*rg.normal(size=(3,5)); Z-=Z.mean(axis=1,keepdims=True)
NP=90
CP=rg.normal(size=(NP,5))+1j*rg.normal(size=(NP,5))
def build(x):
    Pm=(x[:30]+1j*x[30:]).reshape(2,3,5); B=np.zeros((5,4,5),complex); B[0,:3,:]=Pm[0]; B[1,:3,:]=Pm[1]; B[2:,3,:]=Z; return B
def res(x):
    B=build(x); Y=np.tensordot(CP,B,axes=1)
    r1=G(1+Y).sum(axis=1)-120; r2=G(Y).ravel()
    Pm=(x[:30]+1j*x[30:]).reshape(2,15); gm=Pm@Pm.conj().T-np.eye(2)
    out=np.concatenate([r1,r2,gm.ravel()]); return np.concatenate([out.real,out.imag])
hits=[]
for tr in range(NTR):
    x0=rg.normal(size=60)*0.7
    s=least_squares(res,x0,method='lm',xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=8000)
    nr=np.linalg.norm(s.fun)
    if nr<1e-5:
        B=build(s.x); e=check(B,np.random.default_rng(99),npts=60)
        Pm=B[:2,:3,:]; supp=(np.abs(Pm).max(axis=0)>1e-6).astype(int)
        # single-column elements inside P: dim of {c : c0 P0 + c1 P1 supported in one column} -- test each column
        sc=[]
        for j in range(5):
            mask=np.ones((3,5),bool); mask[:,j]=False; M=np.stack([Pm[0][mask],Pm[1][mask]],axis=1)
            sc.append(2-rk(M))
        X=np.zeros((5,5,5),complex); X[:,1:,:]=B; T=T1(X); pr=rk(T.reshape(len(T),5,5)[:,0,:])
        print('trial %2d: res %.1e fresh %.1e | P support (rows x cols) %s | single-column dims per column %s | dim T_1 %d Omega %d'%(tr,nr,e,supp.tolist(),sc,len(T),pr),flush=True)
        np.save('/home/kevxhk/work/L-gct-210/stage2/r9/Pcensus_%d_%d.npy'%(SEED,tr),B); hits.append(tr)
    else:
        print('trial %2d: res %.1e'%(tr,nr),flush=True)
print('hits',len(hits),'of',NTR)
