# Fast relaxation tool: max common isotropic subspace of the Hessian-coefficient forms of perm(J + a x)
# on U_x / C x  (U_x = perp of gradient coefficients), optional extra forms. Analytic-Jacobian LM.
import numpy as np, itertools, os, sys
from scipy.optimize import least_squares
n=5; N=25; idx=[(i,j) for i in range(n) for j in range(n)]
P3=list(itertools.permutations(range(3))); P4=list(itertools.permutations(range(4)))
def perm(A,PP): return sum(np.prod([A[i,p[i]] for i in range(len(p))]) for p in PP)
def hess(X):
    H=np.zeros((N,N),dtype=complex)
    for a,(i,j) in enumerate(idx):
        for b,(k,l) in enumerate(idx):
            if i!=k and j!=l and a<b:
                R=[m for m in range(n) if m not in (i,k)]; C=[m for m in range(n) if m not in (j,l)]
                H[a,b]=H[b,a]=perm(X[np.ix_(R,C)],P3)
    return H
def grad(X): return np.array([perm(np.delete(np.delete(X,i,0),j,1),P4) for (i,j) in idx])
def coeffs(fun,g,deg):
    ss=np.exp(2j*np.pi*np.arange(deg+1)/(deg+1))*0.7
    vals=np.array([fun(np.ones((n,n))+s*g) for s in ss]); V=np.vander(ss,deg+1,increasing=True)
    return np.linalg.solve(V,vals.reshape(deg+1,-1)).reshape((deg+1,)+vals.shape[1:])
def setup(x, extra=()):
    """x: 5x5 element (span level). extra: further fixed elements of L (lists of 5x5). Returns quotient basis Q (25 x N') and forms."""
    fixed=[x]+list(extra)
    Hc=list(coeffs(hess,x,3)); Gc=list(coeffs(grad,x,4))
    G=np.array(Gc).reshape(-1,N)
    # also: L perp grad P_k mixed at fixed elements: use gradients of perm(J+a x+b y) coefficients
    for y in extra:
        for (p,q) in [(i,j) for i in range(5) for j in range(5) if 1<=i+j<=4 and j>=1]:
            pass
    s=np.linalg.svd(G,compute_uv=False); rk=int((s>1e-9*s[0]).sum())
    U=np.linalg.svd(G)[2][rk:].conj().T
    Fx=np.array([f.ravel() for f in fixed]).T
    coef=np.linalg.lstsq(U,Fx,rcond=None)[0]           # fixed elements inside U
    W=np.linalg.svd(coef.T)[2][len(fixed):].conj().T   # complement of fixed in U-coords (bilinear-orthogonal not needed)
    Q=U@W
    Fs=[Q.T@H@Q for H in Hc]
    return Q,Fs,rk
def search(Fs,d,starts=4,nfev=400,seed=0,tol=1e-10,verbose=False):
    rng=np.random.default_rng(seed); Np=Fs[0].shape[0]; iu=np.triu_indices(d); best=np.inf
    for st in range(starts):
        C=np.linalg.qr(rng.normal(size=(Np,Np))+1j*rng.normal(size=(Np,Np)))[0]
        Ys=[C.T@F@C for F in Fs]
        def unpack(v): return (v[:d*(Np-d)]+1j*v[d*(Np-d):]).reshape(d,Np-d)
        def fun(v):
            E=np.hstack([np.eye(d),unpack(v)]); r=np.concatenate([(E@Y@E.T)[iu] for Y in Ys]); return np.concatenate([r.real,r.imag])
        def jac(v):
            E=np.hstack([np.eye(d),unpack(v)]); blocks=[]
            for Y in Ys:
                YE=Y@E.T   # N x d ; (E Y)[a,d+j] = YE[d+j,a] since Y symmetric
                J=np.zeros((d,d,d,Np-d),dtype=complex)   # dR_ab / dX_ij
                for i in range(d):
                    J[i,:,i,:]+=YE[d:,:].T     # delta_ai (Y E^T)_{d+j,b}
                    J[:,i,i,:]+=YE[d:,:].T     # delta_bi (E Y)_{a,d+j}
                blocks.append(J[iu[0],iu[1]].reshape(len(iu[0]),-1))
            Jc=np.vstack(blocks); return np.block([[Jc.real,-Jc.imag],[Jc.imag,Jc.real]])
        v0=rng.normal(size=2*d*(Np-d))*0.5
        m=len(Fs)*len(iu[0]); meth='lm' if m>=d*(Np-d) else 'trf'
        sol=least_squares(fun,v0,jac=jac,method=meth,max_nfev=nfev,xtol=1e-15,ftol=1e-15,gtol=1e-15)
        r=np.linalg.norm(sol.fun)
        if verbose: print('   start',st,'res %.2e'%r,flush=True)
        best=min(best,r)
        if best<tol: break
    return best
def load_space(f):
    B=np.load(f).reshape(-1,25); U,S,Vh=np.linalg.svd(B,full_matrices=False); return Vh[S>1e-3*S[0]]
if __name__=='__main__':
    f=sys.argv[1]; seed=int(sys.argv[2]); ds=[int(a) for a in sys.argv[3:]]
    V=load_space(f); rng=np.random.default_rng(seed)
    c=rng.normal(size=V.shape[0])+1j*rng.normal(size=V.shape[0]); x=(c@V).reshape(n,n); x/=np.linalg.norm(x)
    Q,Fs,rk=setup(x); print(f.split('/')[-1],'grad rank',rk,'quotient dim',Q.shape[1],'form ranks',[np.linalg.matrix_rank(F,1e-8) for F in Fs],flush=True)
    for d in ds: print('  d=%d (level dim %d): best res %.2e'%(d,d+1,search(Fs,d,starts=int(os.environ.get('ST','4')))),flush=True)
