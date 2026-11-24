# (R-LAW) test: for extremal (e+3,e) 4x5 level spaces, do all rows of all elements of N = L' cap {row sums = 0} lie in the defect space C ?
# usage: python3 rlaw_chk.py 'PATTERN' ['PATTERN' ...]      (files: complex arrays (d,4,5))
import sys,glob,collections; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np
from clm import *
from ext_chk import lines
from kc_chk import kernel_colsum
RD=Rdel()
def rk(M,tol=1e-5):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum()) if s.size else 0
tab=collections.defaultdict(list)
for pat in sys.argv[1:]:
    for f in sorted(glob.glob(pat)):
        Z=np.load(f); d=Z.shape[0]; lev,row,col,e=lines(Z)
        if d!=e+3: continue
        r,K=kernel_colsum(Z)
        principal=(K.shape[0]==3 and int((defect_dim(K)>1e-4).sum())==0 and rk(K.sum(2))==3)
        rng=np.random.default_rng(2); A=rng.normal(size=(80,d))+1j*rng.normal(size=(80,d))
        X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X); pk=np.einsum('ns,kjs->nkj',G,RD).reshape(-1,5)
        Cb=np.linalg.svd(pk,full_matrices=False)[2][:e]
        u,s_,vh=np.linalg.svd(Z.sum(2).T,full_matrices=True); rs=int((s_>1e-5).sum()); N=np.einsum('ak,kij->aij',vh[rs:].conj(),Z)
        if len(N)==0: continue
        rows=N.reshape(-1,5); dist=np.abs(rows-(rows@Cb.conj().T)@Cb).max()/np.abs(rows).max()
        colrk=tuple(sorted([rk(K[:,:,j]) for j in range(5)],reverse=True)) if principal else None
        nsr=sum(len(N)-rk(N[:,[i2 for i2 in range(4) if i2!=i],:].reshape(len(N),-1)) for i in range(4))
        tab[(e,principal,colrk,len(N))].append((dist,nsr==len(N),f))
print('(e, principal, column ranks of K = ker c, dim N): count | max rel. distance of the rows of N from C | #with N spanned by single-row elements')
for k in sorted(tab,key=str):
    v=tab[k]; print('  ',k,':',len(v),'| %.1e |'%max(x[0] for x in v),sum(x[1] for x in v))
    if k[1]:
        for x in v:
            if x[0]>1e-6: print('      VIOLATION of (R-LAW):',x[2],'%.1e'%x[0])
