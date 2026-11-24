# single-row parts u_i, single-column parts x_j, neutral columns, rank c, of saved 4x5 spaces (numerical; absolute thresholds)
import sys, glob, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/handoff'); import oracle
def sub_dim(B, mask, tol=1e-6):
    # dim of {Y in span B : Y vanishes outside mask}
    d=len(B); Bf=B.reshape(d,-1); A=Bf[:, ~mask.ravel()].T
    if A.size==0: return d
    s=np.linalg.svd(A,compute_uv=False); return d-int((s>tol*max(1,s[0])).sum())
for f in sys.argv[1:]:
    B=np.load(f); B=B.reshape(len(B),4,5); d=len(B)
    Q,_=np.linalg.qr(B.reshape(d,-1).T); B=Q.T.reshape(d,4,5)
    u=[];x=[]
    for i in range(4):
        m=np.zeros((4,5),bool); m[i]=True; u.append(sub_dim(B,m))
    for j in range(5):
        m=np.zeros((4,5),bool); m[:,j]=True; x.append(sub_dim(B,m))
    rng=np.random.default_rng(0); C=[]
    for t in range(40): C.append(oracle.deletion_vector(np.einsum('d,dab->ab',rng.normal(size=d)+1j*rng.normal(size=d),B)))
    C=np.array(C); s=np.linalg.svd(C,compute_uv=False); e=int((s>1e-6*s[0]).sum())
    neut=[j for j in range(5) if np.abs(C[:,j]).max()<1e-6*np.abs(C).max()]
    cs=B.sum(1); rc=int((np.linalg.svd(cs.reshape(d,-1),compute_uv=False)>1e-6).sum())
    print('%-40s d=%d e=%d u=%s x=%s neutral=%s rank c=%d'%(f.split('/')[-1],d,e,u,x,neut,rc))
