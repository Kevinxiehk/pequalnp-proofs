# stage2: pair-level criterion (zeros allowed) + Type I data + triple test
import numpy as np, itertools
def nullspace(A,tol=1e-9):
    A=np.atleast_2d(A)
    if A.shape[0]==0: return np.eye(A.shape[1],dtype=complex)
    u,s,vh=np.linalg.svd(A); r=int(np.sum(s>tol*max(1,s[0]))) if s.size else 0
    return vh[r:].conj().T
def rank(A,tol=1e-8):
    A=np.atleast_2d(A)
    if A.size==0: return 0
    s=np.linalg.svd(A,compute_uv=False); return int(np.sum(s>tol*max(1,s[0])))
def perm(A):
    A=np.asarray(A); m=A.shape[0]
    if m==0: return 1.0
    return sum(np.prod([A[i,p[i]] for i in range(m)]) for p in itertools.permutations(range(m)))
Qf=np.array([[0,0,0,1],[0,0,1,0],[0,1,0,0],[1,0,0,0]],complex)  # coords (z1j,z1l,z2j,z2l): q=z1j z2l+z1l z2j (as 2x bilinear)
def pair_check(kap,kapp,nu,nup,verbose=False):
    """ThB pair-level test for annihilators (kap,-kapp),(nu,nup). returns list of (T,dim,type,ok)"""
    out=[]; allok=True
    for j,l in itertools.combinations(range(5),2):
        A=np.array([[kap[j],kap[l],-kapp[j],-kapp[l]],[nu[j],nu[l],nup[j],nup[l]]])
        N=nullspace(A); d=N.shape[1]; ell=np.array([kap[j],kap[l],0,0])@N
        B1=np.abs(ell).max()>1e-9
        G=N.T@Qf@N; rk=rank(G,1e-9) if np.abs(G).max()>1e-9 else 0
        if B1:
            ok=(d==2 and rk==1)
            if ok:
                k=nullspace(ell[None,:]); z=N@k[:,0]; ok=np.abs(N.T@Qf@z).max()<1e-8
            typ='B1'
        else:
            ok=True; typ='q0' if rk==0 else 'B2'
        allok=allok and ok; out.append(((j,l),d,typ,rk,ok))
    return allok,out
def gamma_check(kap,kapp,nu,nup):
    """closed-form criterion: G_T=sym(Gamma_T), a_T; returns allok"""
    allok=True; out=[]
    for j,l in itertools.combinations(range(5),2):
        p=lambda i: np.array([kap[i],nu[i]]); pt=lambda i: np.array([-kapp[i],nup[i]])
        R=np.array([[kap[j],kap[l],-kapp[j],-kapp[l]],[nu[j],nu[l],nup[j],nup[l]]])
        rk=rank(R)
        # ell==0 on Pi_T iff (kap_j,kap_l,0,0) in rowspace
        ellzero = rank(np.vstack([R,[kap[j],kap[l],0,0]]))==rk
        Gam=np.outer(p(j),pt(l))+np.outer(p(l),pt(j)); G=(Gam+Gam.T)/2; a=(Gam[0,1]-Gam[1,0])/2
        if rk<2: ok=ellzero
        elif ellzero: ok=True
        else:
            ok = np.abs(G).max()>1e-9 and abs(np.linalg.det(G))<1e-9 and (abs(a)<1e-9 or (abs(G[0,0])<1e-9 and abs(G[0,1])<1e-9))
        allok=allok and ok; out.append(((j,l),rk,ellzero,ok))
    return allok,out
def typeI(kap,eps):
    """Type I data for row annihilator kap (sum 1) and sign vector eps: returns kapp, nu, nup, c, sigma0"""
    eps=np.asarray(eps); k1=kap*(eps>0); k2=kap*(eps<0); K1=k1.sum(); K2=k2.sum(); c=1/(K1-K2)
    kapp=c*(k1-k2); s0=K1*(1-c)
    nu=k1-s0*kap; nup=-c*k1
    return kapp,nu,nup,c,s0
