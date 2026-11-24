# FO2-JOINT test [NOTES-stage2 R10-4]: a level space L containing X lies in T_1(X) and is totally isotropic for EVERY q_m = D^2 perm(J+m),
# m in X, simultaneously (FO2 uses one generic combination only). On the quotient T_1(X)/rad, we ask for a common isotropic subspace of
# dimension D - 5 (X lies in the common radical). Numerical: span of the forms, then LM on the Grassmannian.
# usage: r10_FO2J.py MODE D NTRIAL [SEED]   MODE = calib (5-dim subspace of ex1, D = 7) or a (5,4,5) .npy (rows 1..4)
import sys, itertools, numpy as np
from scipy.optimize import least_squares
A=list(sys.argv); MODE=A[1]; D=int(A[2]); NTRIAL=int(A[3]); SEED=int(A[4]) if len(A)>4 else 1
sys.argv=[A[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
rg=np.random.default_rng(SEED)
if MODE=='calib':
    sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief'); import core
    L7=np.asarray(core.ex1(),complex).reshape(7,25); X=(rg.normal(size=(5,7))+1j*rg.normal(size=(5,7)))@L7
elif MODE.startswith('calibr'):     # calibr_<space>_<row>: X = L_r of a known 7-dim space (dim 3), D must be 7
    sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief'); import core
    _,sp_,rr=MODE.split('_'); rr=int(rr); L7=np.asarray(core.SP[sp_](),complex); L7=L7.reshape(len(L7),5,5)
    R=L7[:,rr,:].reshape(len(L7),5); u_,s_,vh_=np.linalg.svd(R.T); ns=vh_[int((s_>1e-9).sum()):].conj()
    X=(ns@L7.reshape(len(L7),25)); print('known space',sp_,'row',rr,'row-projection dim',int((s_>1e-9).sum()),'dim L_r',len(X))
else:
    Bf=np.load(MODE); X=np.zeros((len(Bf),5,5),complex); X[:,1:,:]=Bf; X=X.reshape(len(Bf),25)
u,s,vh=np.linalg.svd(X,full_matrices=False); dX=int((s>1e-9*s[0]).sum()); X=vh[:dX]
rows=[cof55(np.ones((5,5))+((rg.normal(size=dX)+1j*rg.normal(size=dX))@X).reshape(5,5)) for _ in range(80)]
u,s,vh=np.linalg.svd(np.array(rows)); r=int((s>1e-8*s[0]).sum()); T=vh[r:].conj()        # rows: basis of T_1(X)
Pj=T-(T@X.conj().T)@X; u,s,vh=np.linalg.svd(Pj); Q=vh[:len(T)-dX]; nq=len(Q)               # complement of X in T_1
forms=[]
for _ in range(60):
    m=(rg.normal(size=dX)+1j*rg.normal(size=dX))@X; H=hess(np.ones((5,5))+m.reshape(5,5)); forms.append(Q@H@Q.T)
F=np.array(forms).reshape(len(forms),-1); sv=np.linalg.svd(F,compute_uv=False); N=int((sv>1e-9*sv[0]).sum())
Fb=np.linalg.svd(F)[2][:N].reshape(N,nq,nq)                                                     # basis of the span of the forms
Fb=np.array([(f+f.T)/2 for f in Fb])
rad=nq-np.linalg.matrix_rank(np.vstack(list(Fb)),tol=1e-8)
k=D-dX
print('MODE %s: dim T_1 = %d, complement %d, span of {q_m} has dim N = %d, common radical in the complement %d, need common isotropic dim %d'%(MODE.split('/')[-1],len(T),nq,N,rad,k),flush=True)
iu=np.triu_indices(k)
def res(z):
    C=(z[:k*nq]+1j*z[k*nq:]).reshape(k,nq); out=[]
    for f in Fb:
        M=C@f@C.T; out.append(M[iu])
    G=C@C.conj().T-np.eye(k); out.append(G[iu]); o=np.concatenate(out); return np.concatenate([o.real,o.imag])
for t in range(NTRIAL):
    z=rg.normal(size=2*k*nq); s2=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=int(__import__("os").environ.get("MAXFEV","4000")))
    print('  trial %d: residual %.2e'%(t,np.linalg.norm(s2.fun)),flush=True)
