# Census of (Q-r) solutions inside the Frobenius-Koenig families (there (ii) holds identically, only the level condition remains):
#   X = 5-dim level subspace of {4x5 matrices supported on a mask}, every row projection of dim <= 3.
# For every verified solution: projections, sparse elements, dim T_1, rank q, FO2 bound.
import sys, itertools, numpy as np
from scipy.optimize import least_squares
from collections import Counter
A=list(sys.argv); KIND=A[1]; SEED=int(A[2]); NTR=int(A[3]); MAXIT=int(A[4]) if len(A)>4 else 300
sys.argv=[A[0]]
exec(open('/home/claude/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
P5=np.array(list(itertools.permutations(range(5))))
def perm5(M): return M[...,np.arange(5)[None,:],P5].prod(axis=-1).sum(axis=-1)
MASKS={'24':[[0],[0],[0,1,2,3,4],[0,1,2,3,4]], '33':[[0,1],[0,1],[0,1],[0,1,2,3,4]], '15':[[],[0,1,2,3,4],[0,1,2,3,4],[0,1,2,3,4]], '42':[[2,3,4]]*4}
mask=MASKS[KIND]; rg=np.random.default_rng(SEED)
dims=[min(3,len(m)) for m in mask]; off=[0]
for d,m in zip(dims,mask): off.append(off[-1]+5*d+d*len(m))
NC=off[-1]
def basis(z):
    c=z[:NC]+1j*z[NC:]; B=np.zeros((5,4,5),complex)
    for i,(d,m) in enumerate(zip(dims,mask)):
        if d==0: continue
        U=c[off[i]:off[i]+5*d].reshape(5,d); V=c[off[i]+5*d:off[i+1]].reshape(d,len(m)); B[:,i,m]=U@V
    return B
NP=70; CP=rg.normal(size=(NP,5))+1j*rg.normal(size=(NP,5))
def level(B,C):
    M=np.ones((len(C),5,5),complex); M[:,1:,:]+=np.tensordot(C,B,axes=1); return perm5(M)-120
def res(z):
    B=basis(z); r=level(B,CP); Gm=B.reshape(5,20).conj()@B.reshape(5,20).T-np.eye(5); iu=np.triu_indices(5)
    out=np.concatenate([r.real,r.imag,Gm[iu].real,Gm[iu].imag]); return np.concatenate([out,np.zeros(max(0,2*NC-len(out)))])
def rk2(M,tol=1e-6):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum()) if s.size else 0
fresh=np.random.default_rng(999); cnt=Counter(); nsol=0
for trial in range(NTR):
    z=rg.normal(size=2*NC)*0.5; s=least_squares(res,z,method='lm',xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=MAXIT)
    if np.linalg.norm(s.fun)>1e-9: cnt['no convergence']+=1; continue
    B=basis(s.x); c=fresh.normal(size=(60,5))+1j*fresh.normal(size=(60,5))
    if abs(level(B,c)).max()>1e-7 or rk2(B.reshape(5,20))<5: cnt['spurious/degenerate']+=1; continue
    rows=tuple(rk2(B[:,i,:]) for i in range(4)); cols=tuple(sorted(rk2(B[:,:,j]) for j in range(5)))
    zr=tuple(5-rk2(np.delete(B,i,axis=1).reshape(5,-1)) for i in range(4)); zc=tuple(sorted(5-rk2(np.delete(B,j,axis=2).reshape(5,-1)) for j in range(5)))
    X=np.zeros((5,5,5),complex); X[:,1:,:]=B; n,rho,bd=FO2(X,fresh); nsol+=1
    cnt[('rows',rows,'cols',cols,'single-row',zr,'single-col',zc,'dim T_1',n,'rank',rho,'FO2 bound',bd)]+=1; print('   start',trial,': rows',rows,'single-row',zr,'single-col',zc,'dim T_1',n,'rank',rho,'bound',bd,flush=True)
    if bd>=9: np.save('/tmp/r6_fk_%s_%d_%d.npy'%(KIND,SEED,trial),B)
print('FK(%s): %d verified solutions in %d starts'%(KIND,nsol,NTR))
for k,v in sorted(cnt.items(),key=lambda kv:-kv[1]): print(' ',v,k,flush=True)
