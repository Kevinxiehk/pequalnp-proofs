import numpy as np, sys
n=5
def rank(A,tol=1e-7):
    if A.size==0: return 0
    s=np.linalg.svd(A,compute_uv=False); return int((s>tol*max(1,s[0])).sum())
def invariants(B):
    # B: d x 25 basis rows (t flattened row-major)
    d=B.shape[0]; T=B.reshape(d,n,n)
    rs=T.sum(2); cs=T.sum(1)          # row sums alpha (times n), col sums
    dL=rank(B)
    kap=lambda M: dL-rank(M)          # dim of kernel of map restricted to L
    m=rank(np.hstack([rs,cs])); k=dL-m
    LR=dL-rank(rs); LC=dL-rank(cs)
    # gamma part: t - rowmean - colmean + mean
    G=T-rs[:,:,None]/n-cs[:,None,:]/n+T.sum((1,2))[:,None,None]/n**2
    nu=dL-rank(G.reshape(d,-1))
    return dict(dim=dL,k_DC=k,m_proj=m,rank_alpha=rank(rs),rank_beta=rank(cs),dimRowCentred=LR,dimColCentred=LC,nu_additive=nu,rank_gamma=rank(G.reshape(d,-1)))
def l080():
    basis=[]
    for a in range(3):
        t=np.zeros((n,n)); t[n-1,a]=1; t[n-1,n-2]=-1; basis.append(t.ravel())
    for b in range(n-1):
        t=np.zeros((n,n)); t[b,n-1]=1; t[n-1,n-1]=-1; basis.append(t.ravel())
    return np.array(basis)
print('L080',invariants(l080()))
for f in sys.argv[1:]:
    B=np.load(f); B=B.reshape(B.shape[0],-1) if B.ndim>2 else B
    if B.shape[-1]!=25: B=B.T if B.shape[0]==25 else B
    print(f.split('/')[-1],B.shape,invariants(B))
