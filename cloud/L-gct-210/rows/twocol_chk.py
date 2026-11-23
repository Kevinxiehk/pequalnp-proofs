import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np, glob
from clm import *
rng=np.random.default_rng(0)
def rank(M,tol=1e-7):
    if M.size==0: return 0
    s=np.linalg.svd(M,compute_uv=False); return int(np.sum(s>tol))
n=0
for f in sorted(glob.glob('clm_p4_d*_defect1_s*.npy'))+sorted(glob.glob('seed_d*_e1_t*.npy')):
    Z=np.load(f); d=len(Z); u,s,vh=np.linalg.svd(Z.reshape(d,-1),full_matrices=False); Z=vh.reshape(d,4,5)
    A=rng.normal(size=(300,d))+1j*rng.normal(size=(300,d)); X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X)
    pk=np.einsum('ns,kjs->nkj',G,Rdel()).reshape(-1,5); uu,ss,vv=np.linalg.svd(pk); m=vv[0]
    supp=[j for j in range(5) if abs(m[j])>1e-6*np.abs(m).max()]
    if len(supp)!=2 or abs(m[supp[0]]+m[supp[1]])>1e-6: continue
    a,b=supp; n+=1
    Dab=Z[:,:,a]-Z[:,:,b]                               # (d,4): y_a - y_b of the basis
    rX=rank(Dab); u2,s2,v2=np.linalg.svd(Dab); K=np.einsum('kc,cab->kab',u2[:,rX:].conj().T,Z)   # L'' = kernel
    # zeta: elements supported on columns a,b with y_a = -y_b
    cons=np.concatenate([np.delete(Z,[a,b],axis=2).reshape(d,-1),(Z[:,:,a]+Z[:,:,b])],1); rz=d-rank(cons)
    # strongly level test of L''
    sl=defect_dim(K)[0] if len(K) else 0.0
    # epsilon-orthogonality of X to zeta is implied; report dims
    print('%-28s m = e_%d - e_%d: d=%d  dim zeta=%d  dim X=%d  dim L\'\'=%d  defect of L\'\' (must be 0): %.1e'%(f,a,b,d,rz,rX,len(K),sl))
print('spaces with m = e_a - e_b:',n)
