import numpy as np, sys
def rank(A,tol=1e-6):
    s=np.linalg.svd(A,compute_uv=False); return int((s>tol*max(1,s[0])).sum()), s
def inv(B,n):
    B=B.reshape(-1,n*n); d=B.shape[0]; T=B.reshape(d,n,n)
    rs=T.sum(2); cs=T.sum(1)
    dL,_=rank(B); m,sm=rank(np.hstack([rs,cs])); ra,_=rank(rs); rb,_=rank(cs)
    G=T-rs[:,:,None]/n-cs[:,None,:]/n+T.sum((1,2))[:,None,None]/n**2
    rg,sg=rank(G.reshape(d,-1))
    return dict(dim=dL,k_DC=dL-m,m=m,rank_alpha=ra,rank_beta=rb,RC=dL-ra,CC=dL-rb,nu_additive=dL-rg), np.round(sm,6)
n=int(sys.argv[1])
for f in sys.argv[2:]:
    print(f.split('/')[-1],*inv(np.load(f),n))
