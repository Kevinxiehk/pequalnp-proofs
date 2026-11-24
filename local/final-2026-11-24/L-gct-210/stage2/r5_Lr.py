# Uniform necessary conditions on X = L_r in a 9-dim level space with a_r = 1 (chief RP9 / (Z2)):
#   X is a 5-dim linear space of 4x5 matrices with (i) sum_j perm_4((J' + xi)^(j)) = 120 on X (level) and
#   (ii) perm_4(xi^(j)) = 0 for all five j and all xi in X.
# First-order extension test: L lies in T_1(X) (X placed in rows 1..4 of 5x5 matrices, row 0 = r), so dim T_1(X) >= 9 is necessary.
# LM search for such X from random starts; for every solution: row/column projection dims, single-row dims, dim T_1(X).
import sys, itertools, numpy as np
from scipy.optimize import least_squares
rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1); NT=int(sys.argv[2]) if len(sys.argv)>2 else 4; MAXIT=int(sys.argv[3]) if len(sys.argv)>3 else 150
P4=np.array(list(itertools.permutations(range(4))))
def perm4(A): return A[...,np.arange(4)[None,:],P4].prod(axis=-1).sum(axis=-1)      # A: (...,4,4)
COLS=[[c for c in range(5) if c!=j] for j in range(5)]
def G(Y): return np.stack([perm4(Y[...,:,cols]) for cols in COLS],axis=-1)           # Y: (...,4,5) -> (...,5)
NL=45; NG=24; CL=rg.normal(size=(NL,5))+1j*rg.normal(size=(NL,5)); CG=rg.normal(size=(NG,5))+1j*rg.normal(size=(NG,5))
def res(z):
    B=(z[:100]+1j*z[100:]).reshape(5,4,5)
    lev=G(1+np.tensordot(CL,B,axes=1)).sum(axis=-1)-120; top=G(np.tensordot(CG,B,axes=1)).ravel()
    Gm=B.reshape(5,20).conj()@B.reshape(5,20).T-np.eye(5); iu=np.triu_indices(5)
    r=np.concatenate([lev,top]); return np.concatenate([r.real,r.imag,Gm[iu].real,Gm[iu].imag])
def rk(M,tol=1e-7):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol*max(s[0],1e-300)).sum())
P4b=P4
def cof55(M):
    out=[]
    for i in range(5):
        for j in range(5):
            A=np.delete(np.delete(M,i,axis=0),j,axis=1); out.append(A[np.arange(4)[None,:],P4b].prod(axis=1).sum())
    return out
def dimT1(B,npts=70):
    r2=np.random.default_rng(3); rows=[]
    for _ in range(npts):
        c=r2.normal(size=5)+1j*r2.normal(size=5); M=np.ones((5,5),complex); M[1:]+=np.tensordot(c,B,axes=1); rows.append(cof55(M))
    s=np.linalg.svd(np.array(rows),compute_uv=False); return 25-int((s>1e-8*s[0]).sum())
if __name__=='__main__':
    for trial in range(NT):
        z=rg.normal(size=200)*0.4; s=least_squares(res,z,method='lm',xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=MAXIT)
        nrm=np.linalg.norm(s.fun)
        if nrm>1e-8: print(trial,'no convergence (residual %.1e)'%nrm,flush=True); continue
        B=(s.x[:100]+1j*s.x[100:]).reshape(5,4,5)
        rows=[rk(B[:,i,:]) for i in range(4)]; cols=[rk(B[:,:,j]) for j in range(5)]
        zr=[5-rk(np.delete(B,i,axis=1).reshape(5,-1)) for i in range(4)]; zc=[5-rk(np.delete(B,j,axis=2).reshape(5,-1)) for j in range(5)]
        print(trial,'SOLUTION: row proj dims',rows,' col proj dims',cols,' single-row dims',zr,' single-col dims',zc,' dim T_1 =',dimT1(B),flush=True)
        np.save('/tmp/r5_Lr_%s_%d.npy'%(sys.argv[1] if len(sys.argv)>1 else '1',trial),B)
