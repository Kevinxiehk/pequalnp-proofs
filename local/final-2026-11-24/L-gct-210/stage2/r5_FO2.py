# Second-order extension test (FO2). M a linear subspace of a level space L. For m in M and t in L: perm(J + m + eps t) = 120, so
#   (1) <C(J+m), t> = 0                      (L inside T_1(M));
#   (2) q_m(t,t) = D_t^2 perm(J+m) = 0       (L is totally isotropic for every quadratic form q_m, m in M).
# Hence dim L <= dim T_1(M) - ceil(rank(q_m restricted to T_1(M)) / 2) for every m in M.
import sys, itertools, numpy as np
P4=np.array(list(itertools.permutations(range(4)))); P3=np.array(list(itertools.permutations(range(3))))
def cof55(M):
    out=np.zeros(25,complex)
    for i in range(5):
        for j in range(5):
            A=np.delete(np.delete(M,i,axis=0),j,axis=1); out[5*i+j]=A[np.arange(4)[None,:],P4].prod(axis=1).sum()
    return out
def hess(M):                                    # 25x25 symmetric: H[(i,j),(k,l)] = perm_3(M without rows i,k, columns j,l), i != k, j != l
    H=np.zeros((25,25),complex)
    for i in range(5):
        for k in range(i+1,5):
            rows=[r for r in range(5) if r not in (i,k)]
            for j in range(5):
                for l in range(5):
                    if j==l: continue
                    cols=[c for c in range(5) if c not in (j,l)]; A=M[np.ix_(rows,cols)]; v=A[np.arange(3)[None,:],P3].prod(axis=1).sum()
                    H[5*i+j,5*k+l]=v; H[5*k+l,5*i+j]=v
    return H
def FO2(Mb,rg,npts=70,nm=3,tol=1e-8):
    Mb=np.asarray(Mb,dtype=complex).reshape(len(Mb),25); d=len(Mb); rows=[]
    for _ in range(npts):
        c=rg.normal(size=d)+1j*rg.normal(size=d); rows.append(cof55(np.ones((5,5))+(c@Mb).reshape(5,5)))
    u,s,vh=np.linalg.svd(np.array(rows)); r=int((s>tol*s[0]).sum()); T=vh[r:].conj(); n=len(T); best=0
    for _ in range(nm):
        c=rg.normal(size=d)+1j*rg.normal(size=d); H=hess(np.ones((5,5))+(c@Mb).reshape(5,5)); Q=T@H@T.T      # bilinear (not hermitian) form on T_1 in the basis T
        sv=np.linalg.svd(Q,compute_uv=False); best=max(best,int((sv>1e-7*max(sv[0],1e-300)).sum()))
    # stronger: L is isotropic for every linear combination of the q_m (m in M); use a random combination of 5 of them
    Qc=np.zeros((n,n),complex)
    for _ in range(5):
        c=rg.normal(size=d)+1j*rg.normal(size=d); H=hess(np.ones((5,5))+(c@Mb).reshape(5,5)); Qc+=(rg.normal()+1j*rg.normal())*(T@H@T.T)
    sv=np.linalg.svd(Qc,compute_uv=False); best=max(best,int((sv>1e-7*max(sv[0],1e-300)).sum()))
    return n,best,n-(best+1)//2
if __name__=='__main__':
    rg=np.random.default_rng(1)
    sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief'); import core
    print('sanity on known level spaces (the bound must be >= dim L):')
    for name,sp in core.SP.items():
        B=np.array([np.array(m,dtype=complex) for m in sp()]); d=len(B)
        for sub in (d,d-2):
            Mb=B.reshape(d,25) if sub==d else rg.normal(size=(sub,d))@B.reshape(d,25)
            n,rho,bd=FO2(Mb,rg); print('  %-12s dim L = %d, dim M = %d: dim T_1 = %d, rank q_m on T_1 = %d, bound = %d'%(name,d,sub,n,rho,bd))
