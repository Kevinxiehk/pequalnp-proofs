# The locus b = 0 of the cross family: X(a,0) = {3-dim partial free column 0 on rows 1..4} (+) {e_1 w^T : sum w = 0, <a,w> = 0} (dim 5),
# dim T_1 = 13, FO2 bound 9 (not excluded at second order).  Direct search: level spaces L of dimension D containing X(a,0), L inside T_1:
# unknown D-5 vectors in T_1 (mod X); residual perm(J + l) - 120 at random points of L.  D = 8 and D = 9.
import sys, itertools, numpy as np
from scipy.optimize import least_squares
A=list(sys.argv); D=int(A[1]) if len(A)>1 else 8; NTRIAL=int(A[2]) if len(A)>2 else 6; SEED=int(A[3]) if len(A)>3 else 1
sys.argv=[A[0]]
exec(open('/home/claude/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
rg=np.random.default_rng(SEED)
P5=np.array(list(itertools.permutations(range(5))))
def perm5(M): return M[...,np.arange(5)[None,:],P5].prod(axis=-1).sum(axis=-1)
a=np.array([1,2,3,5],dtype=complex)
# X(a,0)
gens=[]
for yv in ([1,-1,0,0],[0,1,-1,0],[0,0,1,-1]):
    M=np.zeros((5,5),complex); M[1:,0]=yv; gens.append(M)
Cst=np.array([[1,1,1,1],list(a)],dtype=complex); u,s,vh=np.linalg.svd(Cst)
for w in vh[2:].conj():
    M=np.zeros((5,5),complex); M[1,1:]=w; gens.append(M)
X=np.array(gens).reshape(5,25)
rows=[cof55(np.ones((5,5))+((rg.normal(size=5)+1j*rg.normal(size=5))@X).reshape(5,5)) for _ in range(60)]
u,s,vh=np.linalg.svd(np.array(rows)); r=int((s>1e-8*s[0]).sum()); T=vh[r:].conj(); print('dim T_1(X(a,0)) =',len(T))
# complement of X inside T_1
Pj=T-(T@X.conj().T)@np.linalg.solve(X@X.conj().T,X); u,s,vh=np.linalg.svd(Pj); Q=vh[:len(T)-5]           # 8 directions spanning T_1/X
k=D-5; NP=160; CP=rg.normal(size=(NP,D))+1j*rg.normal(size=(NP,D))
def res(z):
    Cc=(z[:k*8]+1j*z[k*8:]).reshape(k,8); E=Cc@Q; Lb=np.vstack([X,E]); M=np.ones((NP,5,5))+(CP@Lb).reshape(NP,5,5)
    r=perm5(M)-120; Gm=Cc@Cc.conj().T-np.eye(k); iu=np.triu_indices(k)
    return np.concatenate([r.real,r.imag,Gm[iu].real,Gm[iu].imag])
best=1e9
for trial in range(NTRIAL):
    z=rg.normal(size=2*k*8); s=least_squares(res,z,method='lm',xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=300)
    nrm=np.linalg.norm(s.fun); best=min(best,nrm)
    print(' D = %d, start %d: residual %.2e'%(D,trial,nrm),flush=True)
print('D =',D,': smallest residual %.2e'%best,'(a level space of dimension D containing X(a,0) would give ~1e-12)')
