# Direct extension search for candidates X = L_r that survive FO2 and (T2): is there a level space of dimension D containing X?
# (Necessarily inside T_1(X).) Unknown: D-5 vectors in T_1(X) modulo X; residual: perm(J + l) - 120 at random points.
import sys, glob, itertools, numpy as np
from scipy.optimize import least_squares
A=list(sys.argv); FILES=A[1].split(','); D=int(A[2]); NTRIAL=int(A[3]) if len(A)>3 else 5
sys.argv=[A[0]]
exec(open('/home/claude/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
P5=np.array(list(itertools.permutations(range(5))))
def perm5(M): return M[...,np.arange(5)[None,:],P5].prod(axis=-1).sum(axis=-1)
rg=np.random.default_rng(5)
for f in FILES:
    B=np.load(f); X=np.zeros((5,5,5),complex); X[:,1:,:]=B; X=X.reshape(5,25)
    u,s,vh=np.linalg.svd(X,full_matrices=False); X=vh[:5]                       # orthonormal basis
    rows=[cof55(np.ones((5,5))+((rg.normal(size=5)+1j*rg.normal(size=5))@X).reshape(5,5)) for _ in range(70)]
    u,s,vh=np.linalg.svd(np.array(rows)); r=int((s>1e-8*s[0]).sum()); T=vh[r:].conj()
    Pj=T-(T@X.conj().T)@X; u,s,vh=np.linalg.svd(Pj); Q=vh[:len(T)-5]; nq=len(Q); k=D-5
    NP=150; CP=rg.normal(size=(NP,D))+1j*rg.normal(size=(NP,D))
    def res(z):
        Cc=(z[:k*nq]+1j*z[k*nq:]).reshape(k,nq); Lb=np.vstack([X,Cc@Q]); M=np.ones((NP,5,5))+(CP@Lb).reshape(NP,5,5)
        rr=perm5(M)-120; Gm=Cc@Cc.conj().T-np.eye(k); iu=np.triu_indices(k)
        return np.concatenate([rr.real,rr.imag,Gm[iu].real,Gm[iu].imag])
    out=[]
    for trial in range(NTRIAL):
        z=rg.normal(size=2*k*nq); s2=least_squares(res,z,method='lm',xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=250); out.append(np.linalg.norm(s2.fun))
    print('%-22s dim T_1 = %d;  level spaces of dimension %d containing X: residuals'%(f.split('/')[-1],len(T),D),' '.join('%.1e'%x for x in out),flush=True)
