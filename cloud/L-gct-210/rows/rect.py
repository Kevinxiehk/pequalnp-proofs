"""LM search / verification for p x 5 level spaces (p=3,4), optional 'degenerate' (all max-minor permanents 0, p=4)."""
import sys, time
import numpy as np
from scipy.optimize import least_squares
Q=5
SUB=[[S for S in range(32) if not (S>>j)&1] for j in range(Q)]
SUB=[np.array(s) for s in SUB]
DEG=np.array([bin(S).count('1') for S in range(32)])
def prodA(X, plus_one=True):
    """X: (npts,p,5) rows as linear forms; returns prod_i (1+l_i) (or prod l_i) in A, shape (npts,32)"""
    npts,p,_=X.shape
    G=np.zeros((npts,32),complex); G[:,0]=1
    for i in range(p):
        Gn=G.copy() if plus_one else np.zeros_like(G)
        for j in range(Q):
            Gn[:,SUB[j]|(1<<j)]+=X[:,i,j][:,None]*G[:,SUB[j]]
        G=Gn
    return G
def Pks(X):
    G=prodA(X); p=X.shape[1]
    return np.stack([G[:,DEG==k].sum(1) for k in range(1,p+1)],1)
def PhiB(X):
    G=prodA(X,False)   # degree p part only
    idx=[31^(1<<j) for j in range(Q)]
    return G[:,idx]
def residual_fn(p,d,degenerate,npts,rng):
    A=rng.normal(size=(npts,d))+1j*rng.normal(size=(npts,d)); A/=np.linalg.norm(A,axis=1)[:,None]
    e=p*Q
    def res(z):
        Z=(z[:e*d]+1j*z[e*d:]).reshape(d,e)
        X=(A@Z).reshape(npts,p,Q)
        P=Pks(X)
        parts=[P[:,:3].ravel() if degenerate else P.ravel()]
        if degenerate: parts.append(PhiB(X).ravel())
        parts.append((Z@Z.conj().T-np.eye(d)).ravel())
        o=np.concatenate(parts); return np.concatenate([o.real,o.imag])
    return res
def run(p,d,degenerate,seed,z0=None,npts=None,maxnfev=4000):
    rng=np.random.default_rng(seed); e=p*Q
    npts=npts or (6*d+30)
    res=residual_fn(p,d,degenerate,npts,rng)
    if z0 is None: z0=rng.normal(size=2*e*d)/np.sqrt(e)
    r=least_squares(res,z0,method='lm',max_nfev=maxnfev,xtol=1e-15,ftol=1e-15,gtol=1e-15)
    Z=(r.x[:e*d]+1j*r.x[e*d:]).reshape(d,p,Q)
    return np.linalg.norm(res(r.x)),Z
def rk(M,tol=1e-7):
    M=np.atleast_2d(M)
    if M.size==0: return 0
    s=np.linalg.svd(M,compute_uv=False); return int(np.sum(s>tol))
def fresh(Z,degenerate,seed=99,n=40):
    rng=np.random.default_rng(seed); d=len(Z)
    A=rng.normal(size=(n,d))+1j*rng.normal(size=(n,d)); A/=np.linalg.norm(A,axis=1)[:,None]
    X=np.einsum('nk,kab->nab',A,Z); v=np.abs(Pks(X)[:,:3]).max() if degenerate else np.abs(Pks(X)).max()
    if degenerate: v=max(v,np.abs(PhiB(X)).max())
    return v
def describe(Z):
    """Z: (d,p,5). row/col projection ranks, dims of zero-row / zero-col subspaces, free-row dims, generic rank"""
    d,p,q=Z.shape
    u_,s_,vh_=np.linalg.svd(Z.reshape(d,-1),full_matrices=False); Z=vh_.reshape(d,p,q)
    rowr=[rk(Z[:,i,:]) for i in range(p)]; colr=[rk(Z[:,:,j]) for j in range(q)]
    free=[d-rk(np.delete(Z,i,axis=1).reshape(d,-1)) for i in range(p)]      # elements supported on row i only
    freec=[d-rk(np.delete(Z,j,axis=2).reshape(d,-1)) for j in range(q)]
    rng=np.random.default_rng(5); c=rng.normal(size=d)+1j*rng.normal(size=d); x=np.einsum('k,kab->ab',c,Z)
    return dict(rowrank=rowr,colrank=colr,freerow=free,freecol=freec,genrank=rk(x),
                rowsumrank=rk(Z.sum(2)),colsumrank=rk(Z.sum(1)))
if __name__=='__main__':
    p=int(sys.argv[1]); d=int(sys.argv[2]); deg=int(sys.argv[3]); s0=int(sys.argv[4]); s1=int(sys.argv[5])
    t0=time.time()
    for s in range(s0,s1):
        rr,Z=run(p,d,deg,s)
        fr=fresh(Z,deg)
        print('p=%d d=%d deg=%d seed %d res %.2e fresh %.1e t=%.0fs'%(p,d,deg,s,rr,fr,time.time()-t0),flush=True)
        if fr<1e-8:
            print('   ',describe(Z),flush=True); np.save('sol_p%d_d%d_g%d_s%d.npy'%(p,d,deg,s),Z)
