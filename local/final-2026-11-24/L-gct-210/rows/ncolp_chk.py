# numerical check of the normal form used in Theorem NCOL-P (principal (4,1) spaces): z_j^V = m_j B_j f, sum_j m_j B_j f = 0, m_n <f,x> = 0
import sys,glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np
from clm import *
from ext_chk import lines
from kc_chk import kernel_colsum
RD=Rdel()
def rk(M,tol=1e-5):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum()) if s.size else 0
worst=[0,0,0,0]; n=0; nproj=0
for pat in sys.argv[1:]:
    for f in sorted(glob.glob(pat)):
        Z=np.load(f); d=Z.shape[0]; lev,row,col,e=lines(Z)
        if (d,e)!=(4,1): continue
        r,K=kernel_colsum(Z)
        if K.shape[0]!=3 or int((defect_dim(K)>1e-4).sum())!=0 or rk(K.sum(2))!=3: continue
        n+=1
        # defect line
        rng=np.random.default_rng(2); A=rng.normal(size=(60,d))+1j*rng.normal(size=(60,d))
        X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X); pk=np.einsum('ns,kjs->nkj',G,RD).reshape(-1,5)
        m=np.linalg.svd(pk,full_matrices=False)[2][0]; m=m/np.abs(m).max()
        # A_j on V: h_j = A_j s(h)
        S=K.sum(2).T                                   # (4,3): columns = s(h_k)
        Aj=[K[:,:,j].T@np.linalg.pinv(S) for j in range(5)]      # 4x4 maps with A_j s(h_k) = (h_k)_j, zero on the complement of V in the pinv sense
        P=np.eye(4)-np.ones((4,4))/4
        Bj=[P-2*Aj[j]@P for j in range(5)]
        worst[3]=max(worst[3],np.abs(sum(Bj)-3*P).max())
        # Z in N = ker s
        u,s_,vh=np.linalg.svd(Z.sum(2).T,full_matrices=True); a=vh[3:].conj()[0]; Zn=np.einsum('k,kij->ij',a,Z)
        kap=(Zn.sum(0)@m.conj())/(m@m.conj())
        zV=P@Zn                                         # columns projected to V
        # f from the column with largest |m_j|: f = B_j^{-1} z_j^V / m_j = B_j^T z_j^V/m_j
        j0=int(np.abs(m).argmax()); fv=Bj[j0].T@zV[:,j0]/m[j0]
        worst[0]=max(worst[0],max(np.linalg.norm(zV[:,j]-m[j]*Bj[j]@fv) for j in range(5))/np.linalg.norm(zV))
        worst[1]=max(worst[1],abs(fv@fv-0.75*kap**2)/abs(kap**2))
        # single-column elements of K
        tot=0
        for nn in range(5):
            oth=[c for c in range(5) if c!=nn]; M=K[:,:,oth].reshape(3,-1)
            uu,ss,vv=np.linalg.svd(M.T,full_matrices=True); rr=int((ss>1e-5).sum()); co=vv[rr:].conj()
            Xn=np.einsum('ak,ki->ai',co,K[:,:,nn]); tot+=len(Xn)
            for x in Xn: worst[2]=max(worst[2],abs(m[nn]*(fv@x))/(np.linalg.norm(fv)*np.linalg.norm(x)))
        nproj+= (tot==3)
print('principal (4,1) spaces:',n,' with K spanned by single-column elements:',nproj)
print('max rel |z_j^V - m_j B_j f| = %.1e;  max rel |<f,f> - (3/4)kappa^2| = %.1e;  max |m_n <f,x>| = %.1e;  max |sum B_j - 3| = %.1e'%tuple(worst))
