# check of Theorem NCOL-P3 ingredients on principal (4,1) spaces: K on columns {a,b,c}; g_j = B_j f; sum g_j = f; |g_j|^2 = |f|^2;
# relation sum_j (m_j - mu) g_j = 0 (mu = m_a+m_b+m_c); conclusion m_a m_b m_c = 0
import sys,glob; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np
from clm import *
from ext_chk import lines
from kc_chk import kernel_colsum
RD=Rdel()
def rk(M,tol=1e-5):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum()) if s.size else 0
w=[0,0,0,0]; n=0; nact=[]
for pat in sys.argv[1:]:
    for f in sorted(glob.glob(pat)):
        Z=np.load(f); d=Z.shape[0]; lev,row,col,e=lines(Z)
        if (d,e)!=(4,1): continue
        r,K=kernel_colsum(Z)
        if K.shape[0]!=3 or int((defect_dim(K)>1e-4).sum())!=0 or rk(K.sum(2))!=3: continue
        n+=1
        rng=np.random.default_rng(2); A=rng.normal(size=(60,d))+1j*rng.normal(size=(60,d))
        X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X); pk=np.einsum('ns,kjs->nkj',G,RD).reshape(-1,5)
        m=np.linalg.svd(pk,full_matrices=False)[2][0]; m=m/np.abs(m).max()
        S=K.sum(2).T; P=np.eye(4)-np.ones((4,4))/4
        Bj=[P-2*(K[:,:,j].T@np.linalg.pinv(S))@P for j in range(5)]
        act=[j for j in range(5) if rk(K[:,:,j])>0]; nact.append(len(act))
        while len(act)<3: act.append([j for j in range(5) if j not in act][0])     # dummy column(s) with B_j = 1
        u,s_,vh=np.linalg.svd(Z.sum(2).T,full_matrices=True); a=vh[3:].conj()[0]; Zn=np.einsum('k,kij->ij',a,Z)
        zV=P@Zn; j0=int(np.abs(m).argmax()); fv=Bj[j0].T@zV[:,j0]/m[j0]; nf=np.linalg.norm(fv)
        g={j:Bj[j]@fv for j in act}; mu=sum(m[j] for j in act)
        w[0]=max(w[0],np.linalg.norm(sum(g.values())-fv)/nf)
        w[1]=max(w[1],max(abs(g[j]@g[j]-fv@fv) for j in act)/abs(fv@fv))
        w[2]=max(w[2],np.linalg.norm(sum((m[j]-mu)*g[j] for j in act))/nf)
        w[3]=max(w[3],abs(np.prod([m[j] for j in act[:nact[-1]]])))
print('principal (4,1) spaces:',n,' numbers of active columns of K:',sorted(set(nact)))
print('max rel |g_a+g_b+g_c - f| = %.1e;  max rel | |g_j|^2 - |f|^2 | = %.1e;  max rel |sum (m_j-mu) g_j| = %.1e;  max |prod_act m_j| = %.1e'%tuple(w))
