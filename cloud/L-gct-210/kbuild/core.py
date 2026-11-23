import numpy as np, itertools
n=5
w=np.exp(2j*np.pi/5); z=np.exp(2j*np.pi/3)
def perm(M):
    k=M.shape[0]
    if k==0: return 1.0
    tot=0
    for p in itertools.permutations(range(k)):
        pr=1
        for i in range(k): pr=pr*M[i,p[i]]
        tot+=pr
    return tot
def Pk(t,k):
    m,nn=t.shape
    if k<0: return 0.0
    if k==0: return 1.0
    tot=0
    for R in itertools.combinations(range(m),k):
        for C in itertools.combinations(range(nn),k):
            tot+=perm(t[np.ix_(R,C)])
    return tot
def grad(t,k):
    m,nn=t.shape; G=np.zeros((m,nn),complex)
    for i in range(m):
        for j in range(nn):
            G[i,j]=Pk(np.delete(np.delete(t,i,0),j,1),k-1)
    return G
u=np.array([1,z**2,z,0,0]); ub=u.conj()
chi=lambda k: w**(k*np.arange(5))
Kb=[np.outer(u,chi(1)),np.outer(u,chi(4)),np.outer(ub,chi(2)),np.outer(ub,chi(3))]
def null(A,tol=1e-9):
    U,s,Vh=np.linalg.svd(A); r=(s>tol*max(1,s[0])).sum(); return Vh[r:].conj().T, s
def E_of(basis,ks=range(1,6),nsamp=None,rng=np.random.default_rng(0)):
    d=len(basis); rows=[]
    nsamp=nsamp or 40
    for _ in range(nsamp):
        a=rng.normal(size=d)+1j*rng.normal(size=d)
        x=sum(ai*b for ai,b in zip(a,basis))
        for k in ks: rows.append(grad(x,k).ravel())
    N,s=null(np.array(rows)); return N
