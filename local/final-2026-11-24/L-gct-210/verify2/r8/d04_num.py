# verify2 r9: numerical cross-check of stage2 R9-6 (D00-3 loci) with MY OWN T_1 / Omega code (brute-force cofactors, bilinear null space).
# Family members rebuilt from the definitions in stage2/r9_direct.py (D003_<pat>_<cho>_<chart>); claim: Omega = C^5 only on the listed loci.
import numpy as np, itertools
rng=np.random.default_rng(21)
def perm(A):
    n=len(A); return sum(np.prod([A[i,s[i]] for i in range(n)]) for s in itertools.permutations(range(n)))
def cof(A):
    return np.array([[perm(np.delete(np.delete(A,i,0),j,1)) for j in range(5)] for i in range(5)])
def rnd(): return rng.normal()+1j*rng.normal()
def member(pat,cho,case,a,b):
    r1,r2=rnd(),rnd(); V=[np.array([1,0,r1,-1-r1]),np.array([0,1,r2,-1-r2])]
    w=np.array([-r1*(3+r1+r2)+(1+r1)*(r1+r2-1),-r2*(3+r1+r2)+(1+r2)*(r1+r2-1),3+r1+r2,r1+r2-1]); Z=np.zeros(4); e34=np.array([0,0,1,-1.])
    if pat=='Q0': Wb=[(V[0],Z),(V[1],Z)]; y3=(e34,Z) if cho=='A' else (Z,w)
    elif pat=='P0': Wb=[(Z,V[0]),(Z,V[1])]; y3=(Z,e34) if cho=='A' else (w,Z)
    else: Wb=[(np.array([1,-1,0,0.]),Z),(Z,np.array([0,0,1,-1.]))]; y3=(np.array([-1,-1,1,1.]),Z) if cho=='A' else (Z,np.array([1,1,-1,-1.]))
    Yb=[(np.ones(4),Z)]+Wb+[y3]; aa=[4,0,0,0]; B=[]
    if case=='i':
        M=np.zeros((5,5),complex); M[1,0]=1; M[2,0]=-1; B.append(M); ph=[a,0,0,b]
        for k,(p,q) in enumerate(Yb):
            M=np.zeros((5,5),complex); M[1,0]=-ph[k]/2; M[2,0]=-ph[k]/2; M[3,0]=-aa[k]; M[4,0]=ph[k]; M[3,1:]=p; M[4,1:]=q; B.append(M)
    else:
        sg=rnd(); M=np.zeros((5,5),complex); M[1,0]=sg; M[2,0]=-1-sg; M[4,0]=1; B.append(M); dd=[a,0,0,b]
        for k,(p,q) in enumerate(Yb):
            M=np.zeros((5,5),complex); M[1,0]=dd[k]; M[2,0]=-dd[k]; M[3,0]=-aa[k]; M[3,1:]=p; M[4,1:]=q; B.append(M)
    return B
def omega(B):
    lev=max(abs(perm(np.ones((5,5))+sum(rnd()*b for b in B))-120) for _ in range(3))
    rows=[cof(np.ones((5,5))+sum(rnd()*b for b in B)).reshape(25) for _ in range(50)]
    u,s,vh=np.linalg.svd(np.array(rows)); r=(s>1e-9*s[0]).sum(); T1=vh[r:].conj().T
    return lev,T1.shape[1],np.linalg.matrix_rank(T1.reshape(5,5,-1)[0],tol=1e-8)
for fam,pts in [('M_A_i',[(None,None),(2,2),(0,0)]),('M_B_i',[(None,None),(0,0)]),('M_A_ii',[(None,None),(0,0)]),('M_B_ii',[(None,None),(0,0)]),
                ('Q0_B_i',[(None,None),(0,None)]),('Q0_B_ii',[(None,None),(0,None)]),('P0_A_i',[(None,None),(0,0),(2,0)])]:
    pat,cho,case=fam.split('_'); out=[]
    for (a,b) in pts:
        aa_=rnd() if a is None else a; bb_=rnd() if b is None else b
        out.append(((a,b),omega(member(pat,cho,case,aa_,bb_))))
    print('%-8s'%fam,'  '.join('%s:(lev %.0e, T1 %d, Om %d)'%(k,v[0],v[1],v[2]) for k,v in out),flush=True)
