# check of the proof of THEOREM NCOL-S (split (4,1) spaces): structure of N = ker kappa
import sys,glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np
from clm import *
RD=Rdel()
def defect_line(Z,ns=60):
    d=Z.shape[0]; rng=np.random.default_rng(2); A=rng.normal(size=(ns,d))+1j*rng.normal(size=(ns,d)); A/=np.linalg.norm(A,axis=1)[:,None]
    X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X); pk=np.einsum('ns,kjs->nkj',G,RD).reshape(-1,5)
    u,s,vh=np.linalg.svd(pk,full_matrices=False); return vh[0].conj() if False else vh[0], s
out=[]
for pat in ('clm_p4_d4_defect1_s*.npy','seed_d4_e1_t*.npy','ncdef_d4_e1_k1_s*.npy'):
    for f in sorted(glob.glob(pat)):
        Z=np.load(f); d=Z.shape[0]
        if d!=4: continue
        m,s=defect_line(Z)
        if s[1]>1e-5*s[0]: continue
        m=m/np.abs(m).max(); zeros=[j for j in range(5) if abs(m[j])<1e-5]; mm=(m*m).sum()
        # split row: e_i m^T in L' ?
        B=Z.reshape(d,-1); isplit=None
        for i in range(4):
            t=np.zeros((4,5),complex); t[i]=m; t=t.ravel()
            c=np.linalg.lstsq(B.T,t,rcond=None)[0]
            if np.linalg.norm(B.T@c-t)<1e-6: isplit=i
        if isplit is None or abs(mm)<1e-6: out.append((f,'non-split or isotropic',len(zeros))); continue
        i=isplit; kap=np.einsum('kj,j->k',Z[:,i,:],m)             # kappa on the basis
        u,ss,vh=np.linalg.svd(kap[None,:]); Nb=np.einsum('ak,kij->aij',vh[1:].conj(),Z)   # basis of ker kappa
        rowi=Nb[:,i,:]; nz=[j for j in range(5) if j not in zeros]
        cs=Z.sum(1)-Z[:,i,:]                                       # column sums of the rows != i, on the basis of L'
        # prediction: row i of N supported on zeros of m; c(Y'') in span(1, e_n (n in zeros)) on L'
        P=np.eye(5)[zeros] if zeros else np.zeros((0,5)); Bs=np.concatenate([np.ones((1,5)),P],0); q,_=np.linalg.qr(Bs.T)
        res_c=np.abs(cs-(cs@q.conj())@q.T).max()
        out.append((f.replace('.npy',''),'zeros of m %s'%zeros,'|row i of N off zeros(m)| %.1e'%np.abs(rowi[:,nz]).max(),'|c(Y\'\') off span(1,e_n)| %.1e'%res_c,'colsum(N) %.1e'%np.abs(Nb.sum(1)).max()))
for o in out: print(o)
