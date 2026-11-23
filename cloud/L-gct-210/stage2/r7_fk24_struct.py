# Structure of the (2,4) solutions: rows 0,1 (of the 4x5 block) = s_1 e_0, s_2 e_0; rows 2,3 = p, q.
# For LM solutions: is s = s_1 + s_2 identically 0 (Case A) or a b = <p',q'> identically (Case B)?  dims of the (p,q)-image Y, of the
# 2-row part {s_1 = s_2 = 0}, single-row / single-column parts, and T_1 / FO2.
import sys, itertools, numpy as np
from scipy.optimize import least_squares
A=list(sys.argv); SEED=int(A[1]); NTR=int(A[2])
sys.argv=[A[0],'24',str(SEED),'0','300']
src=open('/home/claude/work/L-gct-210/stage2/r6_fk.py').read().split("fresh=np.random.default_rng(999)")[0]
exec(src)
SEED=int(A[1]); NTR=int(A[2]); rg=np.random.default_rng(SEED); fresh=np.random.default_rng(999)
def rkk(M,tol=1e-6):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum())
for trial in range(NTR):
    z=rg.normal(size=2*NC)*0.5; s=least_squares(res,z,method='lm',xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=300)
    if np.linalg.norm(s.fun)>1e-9: continue
    B=basis(s.x); c=fresh.normal(size=(60,5))+1j*fresh.normal(size=(60,5))
    if abs(level(B,c)).max()>1e-7 or rkk(B.reshape(5,20))<5: continue
    s1=B[:,0,0]; s2=B[:,1,0]; P=B[:,2,:]; Q=B[:,3,:]
    caseA=np.abs(s1+s2).max()<1e-7
    xi=np.tensordot(c,B,axes=1); a=xi[:,2,1:].sum(axis=1); b=xi[:,3,1:].sum(axis=1); ip=(xi[:,2,1:]*xi[:,3,1:]).sum(axis=1); caseB=np.abs(a*b-ip).max()<1e-7
    Y=np.concatenate([P,Q],axis=1); dY=rkk(Y); two=5-rkk(np.stack([s1,s2],axis=1))          # dim of {s1 = s2 = 0}
    X=np.zeros((5,5,5),complex); X[:,1:,:]=B; n,rho,bd=FO2(X,fresh)
    zr=tuple(5-rkk(np.delete(B,i,axis=1).reshape(5,-1)) for i in range(4)); zc=tuple(5-rkk(np.delete(B,j,axis=2).reshape(5,-1)) for j in range(5))
    print('case A (s=0): %s, case B (ab=<p,q>): %s, dim Y = %d, dim{s1=s2=0} = %d, rows %s, single-row %s, single-col %s, (T_1,rank,bound) = (%d,%d,%d)'%(caseA,caseB,dY,two,tuple(rkk(B[:,i,:]) for i in range(4)),zr,zc,n,rho,bd),flush=True)
    np.save('/tmp/r7_fk24_%d_%d.npy'%(SEED,trial),B)
