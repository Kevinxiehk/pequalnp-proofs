# Kernel condition for N2 blocks. For x in X_ab (rows c,d,e) let C(x) be the symmetric zero-diagonal 5x5 matrix
#   C(x)_{jl} = perm_3(x[cde; [5]-{j,l}]).   (Z2) on L_a = X_ab + C x_b (row b = rho_b) gives at order s^1:  C(x) rho_b = 0 for all x in X_ab
# (and likewise C(x) rho_a = 0).  So an N2 block must have K := common kernel of all C(x) != 0.
# Part 1: K for level blocks found by plain LM (generic non-diagonal and diagonal ones).
# Part 2: LM search for level blocks WITH a kernel vector rho (unknowns psi_c, psi_d, psi_e, rho); classify the solutions.
import sys, itertools, numpy as np
from scipy.optimize import least_squares
from collections import Counter
MODE=sys.argv[2] if len(sys.argv)>2 else 'both'; NTR=int(sys.argv[3]) if len(sys.argv)>3 else 12
sys.argv=[sys.argv[0],sys.argv[1] if len(sys.argv)>1 else '1','0']
src=open('/home/claude/work/L-gct-210/stage2/r4_block.py').read().split("if __name__=='__main__':")[0]
exec(src)
P3=np.array(list(itertools.permutations(range(3))))
PAIRS=[(j,l) for j in range(5) for l in range(j+1,5)]; COMP=[[c for c in range(5) if c not in p] for p in PAIRS]
def Cmats(t):                                   # t: (n,3,5) -> (n,5,5)
    n=len(t); C=np.zeros((n,5,5),complex)
    for (j,l),cols in zip(PAIRS,COMP):
        A=t[:,:,cols]; v=A[:,np.arange(3)[None,:],P3].prod(axis=2).sum(axis=1); C[:,j,l]=v; C[:,l,j]=v
    return C
def kernel(F,npts=40,tol=1e-7):
    r2=np.random.default_rng(5); pts=r2.normal(size=(npts,4))+1j*r2.normal(size=(npts,4)); C=Cmats(elems(F,pts)).reshape(npts*5,5)
    s=np.linalg.svd(C,compute_uv=False); return int((s<tol*s[0]).sum()), s/s[0]
def sparse_info(F):
    B=elems(F,np.eye(4,dtype=complex))            # (4,3,5)
    def rk(M): s=np.linalg.svd(M,compute_uv=False); return int((s>1e-6*max(1,s[0])).sum())
    zc=tuple(4-rk(np.delete(B,j,axis=2).reshape(4,-1)) for j in range(5)); return zc
if MODE in ('both','1'):
    cnt=Counter()
    for trial in range(NTR):
        z=rg.normal(size=60); s=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=600)
        if np.linalg.norm(s.fun)>1e-10: continue
        F=(s.x[:30]+1j*s.x[30:]).reshape(5,3,2); k,sv=kernel(F); cnt[(tuple(sorted(coltype(F[j]) for j in range(5))),'dim K =',k)]+=1
    for k,v in cnt.items(): print('part 1:',v,k,flush=True)
if MODE in ('both','2'):
    PK=rg.normal(size=(12,4))+1j*rg.normal(size=(12,4))
    def res2(z):
        F=(z[:30]+1j*z[30:60]).reshape(5,3,2); rho=z[60:65]+1j*z[65:70]; base=res(np.concatenate([z[:30],z[30:60]]))
        C=Cmats(elems(F,PK)); r=(C@rho).ravel()
        return np.concatenate([base,r.real,r.imag,[np.vdot(rho,rho).real-1]])
    cnt=Counter(); ex={}
    for trial in range(NTR):
        z=rg.normal(size=70); s=least_squares(res2,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=500)
        if np.linalg.norm(s.fun)>1e-9: cnt['no convergence']+=1; continue
        F=(s.x[:30]+1j*s.x[30:60]).reshape(5,3,2); rho=s.x[60:65]+1j*s.x[65:70]
        inj=min(np.linalg.svd(F[:,i,:],compute_uv=False)[-1] for i in range(3))>1e-4
        key=(tuple(sorted(coltype(F[j]) for j in range(5))),'injective' if inj else 'NOT injective','single-col dims',sparse_info(F) if inj else None,'supp rho',tuple(int(abs(x)>1e-6) for x in rho))
        cnt[key]+=1; ex.setdefault(key,s.x)
    for k,v in sorted(cnt.items(),key=lambda kv:-kv[1]): print('part 2:',v,k,flush=True)
    np.save('/tmp/r5_kernel_examples.npy',np.array([ex[k] for k in ex if k!='no convergence'],dtype=float)) if any(k!='no convergence' for k in ex) else None
