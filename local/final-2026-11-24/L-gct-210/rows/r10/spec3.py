# spectrum of A = sum_j rho_3(B_j) (pullback of cubic forms) on the 10-dim space of cubics, for the PL4 base configurations
import numpy as np, itertools
mons=[m for m in itertools.product(range(4),repeat=3) if sum(m)==3]   # exponent vectors of cubic monomials
def pullback(B):
    # matrix of c -> c(Bx) on the monomial basis, computed by evaluation/interpolation
    rng=np.random.default_rng(1); P=rng.normal(size=(30,3))+1j*rng.normal(size=(30,3))
    V=np.array([[np.prod(p**np.array(m)) for m in mons] for p in P])
    M=np.zeros((10,10),complex)
    for k,m in enumerate(mons):
        vals=np.array([np.prod((B@p)**np.array(m)) for p in P])
        M[:,k]=np.linalg.lstsq(V,vals,rcond=None)[0]
    return M
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],float)
def cx(h): a,b,c=h; return np.array([[0,-c,b],[c,0,-a],[-b,a,0]],complex)
c_vec=np.array([1.0 if m==(1,1,1) else 0 for m in mons])
for pat,r in (('++++',np.sqrt(5)),('----',1j*np.sqrt(3))):
    Bs=[(np.eye(3)/4+np.outer(h,h)/4+r*cx(h)/4) if pat=='++++' else (5*np.eye(3)/4-3*np.outer(h,h)/4-r*cx(h)/4) for h in H]
    A=sum(pullback(B) for B in Bs)
    lam0=(A@c_vec)[mons.index((1,1,1))]; resid=np.linalg.norm(A@c_vec-lam0*c_vec)
    ev=np.linalg.eigvals(A)
    print(pat,' A c = lambda0 c with lambda0 = %s (residual %.1e);  needed value n-2 = 2'%(np.round(lam0,6),resid))
    print('   all eigenvalues of A on cubics:',np.round(np.sort_complex(ev),5))
