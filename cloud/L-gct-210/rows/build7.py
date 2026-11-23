import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/rows'); sys.path.insert(0,'/home/claude/work/L-gct-210/numerics')
import numpy as np, itertools
from clm import *
from lib import level_poly
def build(Z,tol=1e-8):
    """Z: (d,4,5) 4x5 level space; returns basis (dim,5,5) of L(L') = L' + e_5 (x) (C(L')+C1)^perp, and defect dim"""
    d=len(Z); rng=np.random.default_rng(3)
    A=rng.normal(size=(200,d))+1j*rng.normal(size=(200,d))
    X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X)
    pk=np.einsum('ns,kjs->nkj',G,Rdel()).reshape(-1,5)
    pk=np.concatenate([pk,np.ones((1,5))*np.abs(pk).max()])
    u,s,vh=np.linalg.svd(pk); r=int(np.sum(s>tol*s[0]))
    W=vh[r:].conj()        # w with pk . w = 0 (bilinear)
    B=[]
    for z in Z:
        M=np.zeros((5,5),complex); M[:4]=z; B.append(M)
    for w in W:
        M=np.zeros((5,5),complex); M[4]=w; B.append(M)
    return np.array(B), r-1
def check(B,n=4,seed=0):
    rng=np.random.default_rng(seed); err=0
    for _ in range(n):
        c=rng.normal(size=len(B))+1j*rng.normal(size=len(B)); t=np.einsum('k,kab->ab',c,B)
        err=max(err,abs(level_poly(t)-120))
    return err
def freeparts(B,tol=1e-7):
    B=np.asarray(B); d=len(B); u,s,vh=np.linalg.svd(B.reshape(d,-1),full_matrices=False); Q=vh.reshape(d,5,5)
    fr=[d-int(np.sum(np.linalg.svd(np.delete(Q,i,axis=0+1).reshape(d,-1),compute_uv=False)>tol)) for i in range(5)]
    fc=[d-int(np.sum(np.linalg.svd(np.delete(Q,j,axis=2).reshape(d,-1),compute_uv=False)>tol)) for j in range(5)]
    rr=[int(np.sum(np.linalg.svd(Q[:,i,:],compute_uv=False)>tol)) for i in range(5)]
    cr=[int(np.sum(np.linalg.svd(Q[:,:,j],compute_uv=False)>tol)) for j in range(5)]
    return dict(free_row_dims=fr,free_col_dims=fc,row_proj_rank=rr,col_proj_rank=cr)
if __name__=='__main__':
    import glob
    from core import invariants, ext_space, fresh_check
    for f in sorted(glob.glob(sys.argv[1])):
        Z=np.load(f); B,e=build(Z)
        print(f,'dim L\' =',len(Z),'defect dim',e,'dim L =',np.linalg.matrix_rank(B.reshape(len(B),-1)),'level err %.1e'%check(B),'fresh P_k %.1e'%fresh_check(B))
        print('   ',freeparts(B)); print('   ',invariants(B),'dim E =',ext_space(B)[0])
