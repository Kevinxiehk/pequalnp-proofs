# Survey of candidates X for L_r (a_r = 1, dim L = 9): 5-dim spaces of 4x5 matrices, level, all 4x4 subpermanents identically 0 (Z2),
# every row projection of dim <= 3 (Lemma C).  For each LM solution: check on FRESH points (level and (Z2)), structure, and the bounds
# FO (dim T_1) and FO2 (dim T_1 - ceil(rank q_m / 2)) on the dimension of a level space containing X.
import sys, itertools, numpy as np
from scipy.optimize import least_squares
A=list(sys.argv); SEED=int(A[1]); NTR=int(A[2]); MAXIT=int(A[3])
sys.argv=[A[0],str(SEED),'0','0']
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_Lr.py').read().split("if __name__=='__main__':")[0])
sys.argv=[A[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
rg=np.random.default_rng(SEED); NL=int(A[4]) if len(A)>4 else 85; NG=int(A[5]) if len(A)>5 else 40; NTR=int(A[2]); MAXIT=int(A[3])
CL=rg.normal(size=(NL,5))+1j*rg.normal(size=(NL,5)); CG=rg.normal(size=(NG,5))+1j*rg.normal(size=(NG,5))
def basis(z):
    c=z[:120]+1j*z[120:]; B=np.zeros((5,4,5),complex)
    for i in range(4):
        U=c[30*i:30*i+15].reshape(5,3); V=c[30*i+15:30*i+30].reshape(3,5); B[:,i,:]=U@V
    return B
def res3(z):
    B=basis(z); lev=G(1+np.tensordot(CL,B,axes=1)).sum(axis=-1)-120; top=G(np.tensordot(CG,B,axes=1)).ravel()
    Gm=B.reshape(5,20).conj()@B.reshape(5,20).T-np.eye(5); iu=np.triu_indices(5)
    r=np.concatenate([lev,top]); return np.concatenate([r.real,r.imag,Gm[iu].real,Gm[iu].imag])
def rk2(M,tol=1e-6):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum())
fresh=np.random.default_rng(999)
for trial in range(NTR):
    z=rg.normal(size=240)*0.5; s=least_squares(res3,z,method='lm',xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=MAXIT)
    nrm=np.linalg.norm(s.fun)
    if nrm>1e-8: print(trial,'no convergence (residual %.1e)'%nrm,flush=True); continue
    B=basis(s.x); c=fresh.normal(size=(60,5))+1j*fresh.normal(size=(60,5))
    dl=abs(G(1+np.tensordot(c,B,axes=1)).sum(axis=-1)-120).max(); dg=abs(G(np.tensordot(c,B,axes=1))).max()
    if dl>1e-7 or dg>1e-7: print(trial,'SPURIOUS (fresh-point defects: level %.1e, Z2 %.1e)'%(dl,dg),flush=True); continue
    rows=[rk2(B[:,i,:]) for i in range(4)]; cols=[rk2(B[:,:,j]) for j in range(5)]
    zr=[5-rk2(np.delete(B,i,axis=1).reshape(5,-1)) for i in range(4)]; zc=[5-rk2(np.delete(B,j,axis=2).reshape(5,-1)) for j in range(5)]
    X=np.zeros((5,5,5),complex); X[:,1:,:]=B; n,rho,bd=FO2(X,fresh)
    print(trial,'SOLUTION: row proj',rows,' col proj',cols,' single-row dims',zr,' single-col dims',zc,' | dim T_1 = %d, rank q_m = %d, FO2 bound = %d'%(n,rho,bd),flush=True)
    np.save('/tmp/r5_Lr4_%d_%d.npy'%(SEED,trial),B)
print('done',flush=True)
