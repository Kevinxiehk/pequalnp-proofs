# As r5_Lr.py, with the REG1 / Lemma C condition built in: every row projection of X = L_r has dim <= 3
# (dim pi_i(L_r) = 5 - lam_ri <= 3).  Parametrisation: row i of the five basis elements = U_i V_i (U_i 5x3, V_i 3x5).
import sys, itertools, numpy as np
from scipy.optimize import least_squares
A=sys.argv; SEED=int(A[1]) if len(A)>1 else 1; NT=int(A[2]) if len(A)>2 else 2; MAXIT=int(A[3]) if len(A)>3 else 300
sys.argv=[A[0],str(SEED),'0','0']
src=open('/home/claude/work/L-gct-210/stage2/r5_Lr.py').read().split("if __name__=='__main__':")[0]
exec(src)
rg=np.random.default_rng(SEED); NT=int(A[2]) if len(A)>2 else 2; MAXIT=int(A[3]) if len(A)>3 else 300
def basis(z):
    c=z[:120]+1j*z[120:]; B=np.zeros((5,4,5),complex)
    for i in range(4):
        U=c[30*i:30*i+15].reshape(5,3); V=c[30*i+15:30*i+30].reshape(3,5); B[:,i,:]=U@V
    return B
def res3(z):
    B=basis(z); lev=G(1+np.tensordot(CL,B,axes=1)).sum(axis=-1)-120; top=G(np.tensordot(CG,B,axes=1)).ravel()
    Gm=B.reshape(5,20).conj()@B.reshape(5,20).T-np.eye(5); iu=np.triu_indices(5)
    r=np.concatenate([lev,top]); out=np.concatenate([r.real,r.imag,Gm[iu].real,Gm[iu].imag])
    return np.concatenate([out,np.zeros(max(0,240-len(out)))])
for trial in range(NT):
    z=rg.normal(size=240)*0.5; s=least_squares(res3,z,method='lm',xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=MAXIT)
    nrm=np.linalg.norm(s.fun)
    if nrm>1e-8: print(trial,'no convergence (residual %.1e)'%nrm,flush=True); continue
    B=basis(s.x)
    rows=[rk(B[:,i,:]) for i in range(4)]; cols=[rk(B[:,:,j]) for j in range(5)]
    zr=[5-rk(np.delete(B,i,axis=1).reshape(5,-1)) for i in range(4)]; zc=[5-rk(np.delete(B,j,axis=2).reshape(5,-1)) for j in range(5)]
    lam=[5-rk(B[:,i,:]) for i in range(4)]
    print(trial,'SOLUTION: dim X =',rk(B.reshape(5,20)),' row proj dims',rows,' col proj dims',cols,' single-row dims',zr,' single-col dims',zc,' dim T_1 =',dimT1(B),flush=True)
    np.save('/tmp/r5_Lr3_%d_%d.npy'%(SEED,trial),B)
print('done',flush=True)
