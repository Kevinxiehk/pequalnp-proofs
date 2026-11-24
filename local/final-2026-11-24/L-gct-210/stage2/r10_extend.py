# Extension search (calibrated): is there a level space of dimension D containing a given 5-dim space X (5x5 matrices)?
# Any such space lies in T_1(X); unknowns = D-5 vectors in a complement of X inside T_1(X); residual perm(J + l) - 120 at NP random points
# plus orthonormality of the added block. usage: r10_extend.py MODE D NTRIAL MAXFEV [SEED]
#   MODE = calib : X = random 5-dim subspace of chief's ex1 (7-dim), D = 7 must be found;   MODE = file path (.npy (5,4,5): rows 1..4).
import sys, itertools, numpy as np
from scipy.optimize import least_squares
A=list(sys.argv); MODE=A[1]; D=int(A[2]); NTRIAL=int(A[3]); MAXFEV=int(A[4]); SEED=int(A[5]) if len(A)>5 else 1
sys.argv=[A[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
P5=np.array(list(itertools.permutations(range(5))))
def perm5(M): return M[...,np.arange(5)[None,:],P5].prod(axis=-1).sum(axis=-1)
rg=np.random.default_rng(SEED)
if MODE=='calib':
    sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief'); import core
    L7=np.asarray(core.ex1(),complex).reshape(7,25); X=(rg.normal(size=(5,7))+1j*rg.normal(size=(5,7)))@L7
else:
    Bf=np.load(MODE); X=np.zeros((len(Bf),5,5),complex); X[:,1:,:]=Bf; X=X.reshape(len(Bf),25)
u,s,vh=np.linalg.svd(X,full_matrices=False); X=vh[:5]
rows=[cof55(np.ones((5,5))+((rg.normal(size=5)+1j*rg.normal(size=5))@X).reshape(5,5)) for _ in range(80)]
u,s,vh=np.linalg.svd(np.array(rows)); r=int((s>1e-8*s[0]).sum()); T=vh[r:].conj()
Pj=T-(T@X.conj().T)@X; u,s,vh=np.linalg.svd(Pj); Q=vh[:len(T)-5]; nq=len(Q); k=D-5
NP=max(160,3*2*k*nq); CP=rg.normal(size=(NP,D))+1j*rg.normal(size=(NP,D))
def res(z):
    Cc=(z[:k*nq]+1j*z[k*nq:]).reshape(k,nq); Lb=np.vstack([X,Cc@Q]); M=np.ones((NP,5,5))+(CP@Lb).reshape(NP,5,5)
    rr=perm5(M)-120; Gm=Cc@Cc.conj().T-np.eye(k); iu=np.triu_indices(k)
    return np.concatenate([rr.real,rr.imag,Gm[iu].real,Gm[iu].imag])
print('MODE %s: dim T_1(X) = %d, complement %d, D = %d, NP = %d'%(MODE.split('/')[-1],len(T),nq,D,NP),flush=True)
for trial in range(NTRIAL):
    z=rg.normal(size=2*k*nq); s2=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=MAXFEV)
    nr=np.linalg.norm(s2.fun); print('  trial %d: residual %.2e  nfev %d'%(trial,nr,s2.nfev),flush=True)
    if nr<1e-8:
        Cc=(s2.x[:k*nq]+1j*s2.x[k*nq:]).reshape(k,nq); Lb=np.vstack([X,Cc@Q])
        CPf=rg.normal(size=(200,D))+1j*rg.normal(size=(200,D)); ff=np.abs(perm5(np.ones((200,5,5))+(CPf@Lb).reshape(200,5,5))-120).max()
        print('  HIT: fresh-point max |perm-120| = %.1e'%ff,flush=True); np.save('/home/kevxhk/work/L-gct-210/stage2/r9/ext_hit_%s_D%d_t%d.npy'%(MODE.split('/')[-1].replace('.npy',''),D,trial),Lb)
