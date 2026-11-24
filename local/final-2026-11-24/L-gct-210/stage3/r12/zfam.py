# Round 12: the split-A Z-family for m0 = (1,1,1,1,-4): Z doubly centred 4x5 (row sums 0, column sums 0), all five columns isotropic
# (<z_j,z_j> = 0, the vartheta(Z) = 0 condition), and the LINE C Z has defect in C m0: for t Z the deletion permanents C_j(tZ) = perm(J_4 + t Z^(j))
# satisfy C_0 = C_1 = C_2 = C_3 and C_4 - 24 = -4 (C_0 - 24) in every degree. Numerical LM on P^11; classify solutions.
import sys, itertools, numpy as np
seed,NS=int(sys.argv[1]),int(sys.argv[2]); rg=np.random.default_rng(seed)
P4=np.array(list(itertools.permutations(range(4))))
def perm4(A): return A[np.arange(4)[None,:],P4].prod(axis=1).sum()
# basis of doubly centred 4x5: E_{ij} - E_{i4} - E_{3j} + E_{34}, i < 3, j < 4
DB=[]
for i in range(3):
    for j in range(4):
        M=np.zeros((4,5)); M[i,j]=1; M[i,4]-=1; M[3,j]-=1; M[3,4]+=1; DB.append(M)
DB=np.array(DB)
TS=np.array([0.7,1.3,-0.9,0.5,-1.6])          # sample t values to separate degrees 3, 4 (degree 1, 2 vanish identically/isotropy)
r0=rg.normal(size=12)+1j*rg.normal(size=12)
def F(x):
    Z=np.tensordot(x,DB,axes=1); out=[Z[:,j]@Z[:,j] for j in range(5)]
    for t in TS[:3]:
        C=np.array([perm4(np.ones((4,4))+t*np.delete(Z,j,axis=1)) for j in range(5)])-24
        out+=[C[1]-C[0],C[2]-C[0],C[3]-C[0],C[4]+4*C[0]]
    out.append(r0@x-1); return np.array(out)
def J(x,h=1e-7):
    f0=F(x); Jm=np.empty((len(f0),12),complex)
    for i in range(12):
        d=np.zeros(12,complex); d[i]=h; Jm[:,i]=(F(x+d)-f0)/h
    return f0,Jm
def lm(x,it=300):
    lam=1e-3; f,Jm=J(x); nf=np.linalg.norm(f)
    for _ in range(it):
        A=Jm.conj().T@Jm; g=Jm.conj().T@f; ok=False
        for _ in range(10):
            d=np.linalg.solve(A+lam*np.eye(12),g); n2=np.linalg.norm(F(x-d))
            if n2<nf: x=x-d; lam=max(lam/4,1e-15); ok=True; break
            lam*=4
        if not ok: break
        f,Jm=J(x); nf=np.linalg.norm(f)
        if nf<1e-13: break
    return x,nf
np.set_printoptions(precision=3,suppress=True,linewidth=150)
kinds={}
for st in range(NS):
    x,nf=lm(rg.normal(size=12)+1j*rg.normal(size=12))
    if nf<1e-10:
        Z=np.tensordot(x,DB,axes=1); Z=Z/np.abs(Z).max(); s=np.linalg.svd(Z,compute_uv=False); rk=int((s>1e-4*s[0]).sum())
        cn=np.linalg.norm(Z,axis=0); supp=tuple(int(c>1e-4) for c in cn)
        Jm=J(x)[1][:-1]; jr=np.linalg.matrix_rank(Jm,1e-7*np.abs(Jm).max())
        key='rank %d, column support %s, local dim <= %d'%(rk,supp,12-1-jr); kinds[key]=kinds.get(key,0)+1
        print('res %.0e sv %s colnorms %s -> %s'%(nf,np.round(s/s[0],6),np.round(cn,6),key))
print('SUMMARY',kinds)
