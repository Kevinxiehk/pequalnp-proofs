import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, glob, itertools
from clm import *
rng=np.random.default_rng(1)
def rank(M,tol=1e-7):
    if M.size==0: return 0
    s=np.linalg.svd(M,compute_uv=False); return int(np.sum(s>tol))
def defect(Z,tol=1e-7):
    d,p,_=Z.shape
    A=rng.normal(size=(60*d+60,d))+1j*rng.normal(size=(60*d+60,d)); X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X)
    pk=np.einsum('ns,kjs->nkj',G,Rdel()).reshape(-1,5); u,s,vh=np.linalg.svd(pk,full_matrices=False); e=int(np.sum(s>tol)); return e,vh[:e]
def level_err(Z):
    d,p,_=Z.shape; A=rng.normal(size=(40,d))+1j*rng.normal(size=(40,d)); A/=np.linalg.norm(A,axis=1)[:,None]
    X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X); return np.abs(G@Rlevel(p).T).max()
# (1) Lemma EC: M = {y_a = y_b} in L', M+ = M + C e_i (e_a - e_b)^T is level, defect = C(M) + C(e_a - e_b)
worst=0; n=0; bad=0
for f in sorted(glob.glob('clm_p4_d[456]_defect*_s*.npy'))[:14]:
    Z=np.load(f); d=len(Z); u,s,vh=np.linalg.svd(Z.reshape(d,-1),full_matrices=False); Z=vh.reshape(d,4,5)
    for a,b in ((0,1),(1,3),(2,4)):
        Dm=Z[:,:,a]-Z[:,:,b]; rD=rank(Dm); u2,s2,v2=np.linalg.svd(Dm); M=np.einsum('kc,cab->kab',u2[:,rD:].conj().T,Z)
        if len(M)==0: continue
        eM,CM=defect(M)
        for i in (0,3):
            E=np.zeros((1,4,5),complex); E[0,i,a]=1; E[0,i,b]=-1; Mp=np.concatenate([M,E]); ep,Cp=defect(Mp)
            v=np.zeros(5); v[a]=1; v[b]=-1
            pred=rank(np.concatenate([CM,v[None,:]/np.sqrt(2)])) if eM else 1
            worst=max(worst,level_err(Mp)); n+=1; bad+=(ep!=pred)
print('Lemma EC on %d cases: max level error of M + C e_i(e_a-e_b)^T = %.1e; defect dim != dim(C(M) + C(e_a-e_b)) in %d cases'%(n,worst,bad))
# (2) tower: L' = L(L'') for 3x5 level L'' (rho = 0): defect of L'
for f in sorted(glob.glob('di_p3_d*_e*_s*.npy'))[:25:3]:
    Z3=np.load(f); d3=len(Z3); e3,C3=defect(Z3)
    W=np.linalg.svd(np.concatenate([C3,np.ones((1,5))/np.sqrt(5)]))[2][e3+1:].conj()
    B=[]
    for z in Z3:
        Mx=np.zeros((4,5),complex); Mx[:3]=z; B.append(Mx)
    for w in W:
        Mx=np.zeros((4,5),complex); Mx[3]=w; B.append(Mx)
    L4=np.array(B); e4,C4=defect(L4)
    nondeg=rank(C3@C3.T) if e3 else 0
    print('%-22s L\'\' (d,e)=(%d,%d), rank of dot form on C(L\'\') = %d  ->  L\' = L(L\'\') 4x5: dim %d, level err %.0e, defect %d'%(f,d3,e3,nondeg,len(L4),level_err(L4),e4))
