# numerical exploration of S_4: single strongly level 4x5 matrices with column 4 = 0, four active columns (Walsh coordinates)
import numpy as np, itertools, sys
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],dtype=complex)
def perm(M):
    n=M.shape[0]; s=0
    for p in itertools.permutations(range(n)):
        s+=np.prod([M[i,p[i]] for i in range(n)])
    return s
def C(Y):  # deletion vector c(Y)_j = perm(J+Y without col j) - 24
    J=np.ones((4,5))
    return np.array([perm((J+Y)[:,[c for c in range(5) if c!=j]])-24 for j in range(5)])
def mat(x):  # x: 12 complex -> 4x5 matrix
    X=x.reshape(4,3); Y=np.zeros((4,5),dtype=complex); Y[:,:4]=H@X.T; return Y
SS=np.array([0.5,1.0,-0.7,1.3])
VM=np.array([[s**k for k in range(1,5)] for s in SS])
VMi=np.linalg.inv(VM)
def homog(Y):  # coefficients of degree 2,3,4 of C(sY) (degree 1 vanishes in Walsh coords)
    Cs=np.array([C(s*Y) for s in SS]); co=VMi@Cs; return co[1:].ravel()
def res(x,ell):
    Y=mat(x); r=list(homog(Y)); r.append(ell@x-1); return np.array(r)
def jac(x,ell,h=1e-7):
    f0=res(x,ell); Jm=np.zeros((len(f0),len(x)),dtype=complex)
    for k in range(len(x)):
        e=np.zeros(len(x),dtype=complex); e[k]=h; Jm[:,k]=(res(x+e,ell)-f0)/h
    return Jm
def lm(x,ell,it=200):
    lam=1e-3
    for _ in range(it):
        f=res(x,ell); nf=np.linalg.norm(f)
        if nf<1e-13: break
        Jm=jac(x,ell); A=Jm.conj().T@Jm; g=Jm.conj().T@f
        dx=np.linalg.solve(A+lam*np.eye(len(x)),-g)
        if np.linalg.norm(res(x+dx,ell))<nf: x=x+dx; lam=max(lam/3,1e-12)
        else: lam*=4
    return x,np.linalg.norm(res(x,ell))
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
out=[]
for trial in range(int(sys.argv[2]) if len(sys.argv)>2 else 20):
    x=rng.normal(size=12)+1j*rng.normal(size=12); ell=rng.normal(size=12)+1j*rng.normal(size=12)
    x,r=lm(x,ell)
    if r<1e-10:
        X=x.reshape(4,3); nrm=[np.linalg.norm(X[j]) for j in range(4)]
        Jm=jac(x,ell); sv=np.linalg.svd(Jm[:-1],compute_uv=False)
        rk=int(np.sum(sv>1e-6*sv[0]))
        G=X@X.T; sig=X.sum(0)
        print('hit res %.1e colnorms %s  rank(jac of c)=%d (tangent dim %d)  Gram offdiag %s  sig.sig %.3g'%(r,np.round(nrm,3),rk,12-rk,np.round([G[0,1],G[2,3],G[0,2],G[1,3],G[0,3],G[1,2]],4),abs(sig@sig)),flush=True)
        out.append(x)
np.save('s4pts_%s.npy'%(sys.argv[1] if len(sys.argv)>1 else 0),np.array(out))
