# Round 11: two-row and two-column pieces over the census of 6-dim level spaces (the file list of bispan_all.py + dr35 spaces):
# for every row pair (r,j): dim X_0 (row-r projection of the sum-zero part P_0), line elements, and rank of B (when no row-j line elements).
import sys, glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, collections
from pieces import sub_supported
from ext6 import F45
src=open('/home/kevxhk/work/L-gct-210/reg2/bispan_all.py').read(); files=eval(src.split('files=')[1].split('\n')[0])
files+=sorted(glob.glob('dr35_u*_s*.npy'))
def null(A,tol=1e-8):
    u,s,vh=np.linalg.svd(A); r=int((s>tol*max(1,s[0] if len(s) else 1)).sum()); return vh[r:].conj()
stats=collections.Counter(); examples={}
nsp=0
for f in files:
    try: M=np.load(f)
    except Exception: continue
    if M.ndim!=3 or M.shape[1:]!=(4,5) or np.linalg.matrix_rank(M.reshape(len(M),-1),tol=1e-8)!=6: continue
    M=M/np.abs(M).max(); rg=np.random.default_rng(0); C=rg.normal(size=(20,len(M)))+1j*rg.normal(size=(20,len(M)))
    if np.abs(F45(np.einsum('nk,kij->nij',C,M))-120).max()>1e-6: continue
    nsp+=1
    for r in range(4):
        for j in range(4):
            if r==j: continue
            mask=np.zeros((4,5),bool); mask[r]=True; mask[j]=True
            P=sub_supported(M,mask)
            if len(P)==0: continue
            # robust version (round 11): split off the line elements (sub_supported, tol 1e-7) before imposing S x = 0
            mr=np.zeros((4,5),bool); mr[r]=True; Lr=sub_supported(M,mr); mj=np.zeros((4,5),bool); mj[j]=True; Lj=sub_supported(M,mj)
            lr,lj=len(Lr),len(Lj)
            Lsp=np.concatenate([Lr,Lj],0).reshape(lr+lj,-1) if lr+lj else np.zeros((0,20))
            Pf=P.reshape(len(P),-1)
            if lr+lj:
                Qb=np.linalg.qr(Lsp.T)[0]; Rest=Pf-(Pf@Qb.conj())@Qb.T
                u_,s_,vh_=np.linalg.svd(Rest); Rest=vh_[:int((s_>1e-7).sum())]
            else: Rest=Pf
            Rest=Rest.reshape(-1,4,5)
            if len(Rest):
                sv=Rest[:,r,:].sum(1); c0=null(sv[None,:],1e-6) if np.abs(sv).max()>1e-6 else np.eye(len(Rest))
                R0=np.einsum('kc,cab->kab',c0,Rest)
            else: R0=np.zeros((0,4,5))
            dR=np.linalg.matrix_rank(R0[:,r,:],tol=1e-6) if len(R0) else 0
            dX=lr+dR; rkB=dR
            P0=np.zeros(lr+lj+len(R0))
            key=(dX,rkB); stats[key]+=1
            if dX>=3 or rkB>=2: examples.setdefault(key,[]).append('%s rows(%d,%d) P=%d P0=%d lines r:%d j:%d'%(f,r,j,len(P),len(P0),lr,lj))
print('spaces:',nsp)
for k in sorted(stats): print('dim X0 = %d, rank B = %d : %d (ordered row pairs)'%(k[0],k[1],stats[k]))
for k in sorted(examples):
    print('examples',k,':'); [print('   ',e) for e in examples[k][:4]]
