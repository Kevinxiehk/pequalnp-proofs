# Case lam_{rr'} = 5 (L_r = L_r' =: X, a 5-dim level space on the other three rows). Then row r' of u in L^ is Phi(u_r) with Phi in GL_5,
# Phi(1) = 1, and perm(u) = u_r^T C(u'') Phi u_r, C(M)_{jl} = perm_3(M without columns j,l).  The part of degree 3 in xi in X gives
#   (Phi3)   C(xi) Phi + Phi^T C(xi) = 0   for all xi in X.
# For a given X: solve the linear system (Phi3) for Phi (25 unknowns) and report the solution space, invertibility and Phi(1) = 1.
import sys, glob, itertools, numpy as np
P3=np.array(list(itertools.permutations(range(3))))
PAIRS=[(j,l) for j in range(5) for l in range(j+1,5)]; COMP=[[c for c in range(5) if c not in p] for p in PAIRS]
def Cmat(x):                                   # x: (3,5) -> 5x5 symmetric zero diagonal
    C=np.zeros((5,5),complex)
    for (j,l),cols in zip(PAIRS,COMP):
        A=x[:,cols]; v=A[np.arange(3)[None,:],P3].prod(axis=1).sum(); C[j,l]=v; C[l,j]=v
    return C
rg=np.random.default_rng(1)
for f in sorted(glob.glob('/tmp/r6_fk_15_*.npy')):
    B=np.load(f); rows3=[i for i in range(4) if np.abs(B[:,i,:]).max()>1e-8]; X=B[:,rows3,:]            # (5,3,5)
    eqs=[]
    for _ in range(40):
        c=rg.normal(size=5)+1j*rg.normal(size=5); C=Cmat(np.tensordot(c,X,axes=1))
        for j in range(5):
            for m in range(j,5):
                row=np.zeros((5,5),complex)                # coefficient of Phi[l,k] in (C Phi + Phi^T C)[j,m] = sum_l C[j,l] Phi[l,m] + sum_l Phi[l,j] C[l,m]
                row[:,m]+=C[j,:]; row[:,j]+=C[:,m]; eqs.append(row.ravel())
    A=np.array(eqs); u,s,vh=np.linalg.svd(A); r=int((s>1e-8*s[0]).sum()); ns=vh[r:].conj()
    # span of the C(xi)
    Cs=np.array([Cmat(np.tensordot(rg.normal(size=5)+1j*rg.normal(size=5),X,axes=1))[np.triu_indices(5,1)] for _ in range(40)]); dc=np.linalg.matrix_rank(Cs,tol=1e-8)
    print(f.split('/')[-1],': dim span{C(xi)} =',dc,'of 10;  solution space of (Phi3): dim',len(ns))
    if len(ns):
        # is there an invertible solution with Phi 1 = 1 ?  generic element of the solution space
        best=0
        for _ in range(20):
            Phi=((rg.normal(size=len(ns))+1j*rg.normal(size=len(ns)))@ns).reshape(5,5); sv=np.linalg.svd(Phi,compute_uv=False); best=max(best,sv[-1]/sv[0])
        ones=np.array([p.reshape(5,5)@np.ones(5) for p in ns]).T           # 5 x dim: images of 1
        # solve ones @ c = 1
        c,res_,rk_,_=np.linalg.lstsq(ones,np.ones(5,dtype=complex),rcond=None); err=np.linalg.norm(ones@c-1)
        print('   generic solution: smallest/largest singular value %.1e (0 = never invertible);  Phi(1) = 1 solvable: residual %.1e'%(best,err))
