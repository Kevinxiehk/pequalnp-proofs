import numpy as np, itertools, sys
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
def grad(X):
    return np.array([perm(np.delete(np.delete(X,i,0),j,1),P4) for (i,j) in idx])
def coeffs(fun,g,deg):
    ss=np.exp(2j*np.pi*np.arange(deg+1)/(deg+1))*0.7
    vals=np.array([fun(np.ones((n,n))+s*g) for s in ss])
    V=np.vander(ss,deg+1,increasing=True); return np.linalg.solve(V,vals.reshape(deg+1,-1)).reshape((deg+1,)+vals.shape[1:])
Bdc=np.load(__import__('os').environ.get('GFILE','/home/claude/work/L-gct-086/smallcases/sol_n5_d2_dc_s5.npy')).reshape(-1,25)
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
c=rng.normal(size=Bdc.shape[0])+1j*rng.normal(size=Bdc.shape[0]); g=(c@Bdc).reshape(n,n); g/=np.linalg.norm(g)
Hc=coeffs(hess,g,3); Gc=coeffs(grad,g,4)
# U = orth complement (bilinear, not hermitian) of gradient coefficient vectors
G=Gc.reshape(5,N); s=np.linalg.svd(G,compute_uv=False); print('rank grads',int((s>1e-9*s[0]).sum()))
_,_,Vh=np.linalg.svd(G); rk=int((s>1e-9*s[0]).sum()); U=Vh[rk:].conj().T   # columns u with G u = 0
gv=g.ravel(); print('g in U?',np.linalg.norm(G@gv))
# quotient by g: complement of g inside U
coef=np.linalg.lstsq(U,gv,rcond=None)[0]; _,_,W=np.linalg.svd(coef[None,:]); Ubar=U@W[1:].conj().T
Fs=[Ubar.T@H@Ubar for H in Hc]
for F in Fs: 
    sv=np.linalg.svd(F,compute_uv=False); print('form rank',int((sv>1e-9*sv[0]).sum()),'of',F.shape[0])
Np=Ubar.shape[1]
def run(d,starts=int(__import__('os').environ.get('ST','6'))):
    best=1e9
    for st in range(starts):
        Rb=np.linalg.qr(rng.normal(size=(Np,Np))+1j*rng.normal(size=(Np,Np)))[0]
        Fr=[Rb.T@F@Rb for F in Fs]
        def res(x):
            X=(x[:d*(Np-d)]+1j*x[d*(Np-d):]).reshape(d,Np-d); Bm=np.hstack([np.eye(d),X])
            r=np.concatenate([(Bm@F@Bm.T)[np.triu_indices(d)] for F in Fr]); return np.concatenate([r.real,r.imag])
        x0=rng.normal(size=2*d*(Np-d))*0.5
        sol=least_squares(res,x0,method=('lm' if 2*4*d*(d+1)//2>=2*d*(Np-d) else 'trf'),max_nfev=int(__import__('os').environ.get('NF','2500')))
        best=min(best,np.linalg.norm(sol.fun)); print('  start',st,'res %.2e'%np.linalg.norm(sol.fun),'nfev',sol.nfev,flush=True)
        if best<1e-9: break
    return best
for d in [int(a) for a in sys.argv[2:]]:
    print('common isotropic in U/g of dim',d,'(level dim',d+1,') best residual %.2e'%run(d))
