# verify2 r9: numerical cross-check of stage2 R9-6 (D00-3 loci) with MY OWN T_1 / Omega code (brute-force cofactors, bilinear null space).
# Family members rebuilt from the definitions in stage2/r9_direct.py (D003_<pat>_<cho>_<chart>); claim: Omega = C^5 only on the listed loci.
import numpy as np, itertools
rng=np.random.default_rng(21)
def perm(A):
    n=len(A); return sum(np.prod([A[i,s[i]] for i in range(n)]) for s in itertools.permutations(range(n)))
def cof(A):
    return np.array([[perm(np.delete(np.delete(A,i,0),j,1)) for j in range(5)] for i in range(5)])
def rnd(): return rng.normal()+1j*rng.normal()
def member(pat,cho,ch,u1):
    r1,r2=rnd(),rnd(); V=[np.array([1,0,r1,-1-r1]),np.array([0,1,r2,-1-r2])]
    w=np.array([-r1*(3+r1+r2)+(1+r1)*(r1+r2-1),-r2*(3+r1+r2)+(1+r2)*(r1+r2-1),3+r1+r2,r1+r2-1]); Z=np.zeros(4); e34=np.array([0,0,1,-1.])
    if pat=='Q0': Wb=[(V[0],Z),(V[1],Z)]; y3=(e34,Z) if cho=='A' else (Z,w)
    elif pat=='P0': Wb=[(Z,V[0]),(Z,V[1])]; y3=(Z,e34) if cho=='A' else (w,Z)
    else: Wb=[(np.array([1,-1,0,0.]),Z),(Z,np.array([0,0,1,-1.]))]; y3=(np.array([-1,-1,1,1.]),Z) if cho=='A' else (Z,np.array([1,1,-1,-1.]))
    cvec=[np.array([1,-1,0,0.]),np.array([-.5,-.5,1,0]),np.array([-.5,-.5,0,1])]
    k1,k2=rnd(),rnd()
    Kb={'3':[[1,0,-k1],[0,1,-k2]],'2':[[1,-k1,0],[0,0,1]],'1':[[0,1,0],[0,0,1]]}[ch]; comp={'3':2,'2':1,'1':0}[ch]
    B=[]
    for kb in Kb:
        M=np.zeros((5,5),complex); M[1:,0]=sum(kb[i]*cvec[i] for i in range(3)); B.append(M)
    for (p,q) in Wb:
        M=np.zeros((5,5),complex); M[3,1:]=p; M[4,1:]=q; B.append(M)
    M=np.zeros((5,5),complex); M[1:,0]=u1*cvec[comp]; M[3,1:]=y3[0]; M[4,1:]=y3[1]; B.append(M)
    return B
def omega(B):
    lev=max(abs(perm(np.ones((5,5))+sum(rnd()*b for b in B))-120) for _ in range(3))
    rows=[cof(np.ones((5,5))+sum(rnd()*b for b in B)).reshape(25) for _ in range(50)]
    u,s,vh=np.linalg.svd(np.array(rows)); r=(s>1e-9*s[0]).sum(); T1=vh[r:].conj().T
    return lev,T1.shape[1],np.linalg.matrix_rank(T1.reshape(5,5,-1)[0],tol=1e-8)
for fam in ['M_A_1','M_A_2','M_B_1','M_B_2','Q0_A_1','Q0_B_1','Q0_B_2','P0_A_1','P0_B_1','P0_B_2','Q0_A_3','P0_A_3','M_A_3']:
    pat,cho,ch=fam.split('_')
    res=[omega(member(pat,cho,ch,rnd())) for _ in range(2)]
    res0=omega(member(pat,cho,ch,0.0))
    print('%-7s u1 random: (lev, dimT1, dimOmega) = %s   | u1 = 0: %s'%(fam,[(('%.0e'%a),b,c) for a,b,c in res],(('%.0e'%res0[0]),res0[1],res0[2])),flush=True)
