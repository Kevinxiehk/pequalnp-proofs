# Census of solutions of (Q-r): 5-dim spaces X of 4x5 matrices, level, all 4x4 column-deletion subpermanents identically zero,
# row projections of dim <= DMAX (parametrised as U_i V_i).  Each LM solution is verified on fresh points; then: projection dims,
# sparse elements, common zero block (Frobenius-Koenig type), dim T_1, rank q, FO2 bound, and dim of the row-r projection of T_1.
import sys, itertools, numpy as np
from scipy.optimize import least_squares
A=list(sys.argv); SEED=int(A[1]); NTR=int(A[2]); MAXIT=int(A[3]); DM=[int(c) for c in A[4]] if len(A)>4 else [3,3,3,3]
sys.argv=[A[0],str(SEED),'0','0']
exec(open('/home/claude/work/L-gct-210/stage2/r5_Lr.py').read().split("if __name__=='__main__':")[0])
sys.argv=[A[0]]
exec(open('/home/claude/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
rg=np.random.default_rng(SEED); NL=50; NG=28; NTR=int(A[2]); MAXIT=int(A[3]); DM=[int(c) for c in A[4]] if len(A)>4 else [3,3,3,3]
CL=rg.normal(size=(NL,5))+1j*rg.normal(size=(NL,5)); CG=rg.normal(size=(NG,5))+1j*rg.normal(size=(NG,5))
off=[0]; 
for d in DM: off.append(off[-1]+10*d)
NC=off[-1]
def basis(z):
    c=z[:NC]+1j*z[NC:]; B=np.zeros((5,4,5),complex)
    for i,d in enumerate(DM):
        U=c[off[i]:off[i]+5*d].reshape(5,d); V=c[off[i]+5*d:off[i]+10*d].reshape(d,5); B[:,i,:]=U@V
    return B
def res3(z):
    B=basis(z); lev=G(1+np.tensordot(CL,B,axes=1)).sum(axis=-1)-120; top=G(np.tensordot(CG,B,axes=1)).ravel()
    Gm=B.reshape(5,20).conj()@B.reshape(5,20).T-np.eye(5); iu=np.triu_indices(5)
    r=np.concatenate([lev,top]); out=np.concatenate([r.real,r.imag,Gm[iu].real,Gm[iu].imag])
    return np.concatenate([out,np.zeros(max(0,2*NC-len(out)))])
def rk2(M,tol=1e-6):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum())
def zero_block(B,tol=1e-6):
    Z=(np.abs(B).max(axis=0)<tol); best=(0,0)
    for s in range(1,5):
        for rows in itertools.combinations(range(4),s):
            cols=[j for j in range(5) if all(Z[i,j] for i in rows)]
            if s+len(cols)>sum(best) and len(cols)>0: best=(s,len(cols))
    return best
fresh=np.random.default_rng(999)
for trial in range(NTR):
    z=rg.normal(size=2*NC)*0.5; s=least_squares(res3,z,method='lm',xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=MAXIT)
    nrm=np.linalg.norm(s.fun)
    if nrm>1e-8: print(trial,'no convergence (residual %.1e)'%nrm,flush=True); continue
    B=basis(s.x); c=fresh.normal(size=(80,5))+1j*fresh.normal(size=(80,5))
    dl=abs(G(1+np.tensordot(c,B,axes=1)).sum(axis=-1)-120).max(); dg=abs(G(np.tensordot(c,B,axes=1))).max()
    if dl>1e-7 or dg>1e-7 or rk2(B.reshape(5,20))<5: print(trial,'SPURIOUS (level %.1e, Z2 %.1e, dim %d)'%(dl,dg,rk2(B.reshape(5,20))),flush=True); continue
    rows=[rk2(B[:,i,:]) for i in range(4)]; cols=[rk2(B[:,:,j]) for j in range(5)]
    zr=[5-rk2(np.delete(B,i,axis=1).reshape(5,-1)) for i in range(4)]; zc=[5-rk2(np.delete(B,j,axis=2).reshape(5,-1)) for j in range(5)]
    X=np.zeros((5,5,5),complex); X[:,1:,:]=B; n,rho,bd=FO2(X,fresh)
    print(trial,'SOLUTION: row proj',rows,' col proj',cols,' single-row',zr,' single-col',zc,' zero block',zero_block(B),' | dim T_1 = %d, rank = %d, FO2 bound = %d'%(n,rho,bd),flush=True)
    np.save('/tmp/r6_census_%d_%d.npy'%(SEED,trial),B)
print('done',flush=True)
