import numpy as np, itertools, sys
def perm(A):
    n=A.shape[0]; return sum(np.prod([A[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n)))
def genuine(B,n):
    B=B.reshape(-1,n*n); U,S,Vh=np.linalg.svd(B,full_matrices=False)
    keep=[k for k in range(len(S)) if S[k]>1e-3*S[0]]
    V=Vh[keep]; rng=np.random.default_rng(0)
    err=max(abs(perm(np.ones((n,n))+np.tensordot(rng.normal(size=len(keep))+1j*rng.normal(size=len(keep)),V.reshape(-1,n,n),1))-math.factorial(n)) for _ in range(3))
    return V,err
import math
def rk(A,tol=1e-6):
    s=np.linalg.svd(A,compute_uv=False); return int((s>tol*max(1,s[0])).sum()) if s.size else 0
def inv(V,n):
    d=V.shape[0]; T=V.reshape(d,n,n); rs=T.sum(2); cs=T.sum(1)
    m=rk(np.hstack([rs,cs])); G=T-rs[:,:,None]/n-cs[:,None,:]/n+T.sum((1,2))[:,None,None]/n**2
    g=rk(G.reshape(d,-1)); return dict(d=d,k=d-m,m=m,dimGamma=g,ra=rk(rs),rb=rk(cs))
n=int(sys.argv[1])
for f in sys.argv[2:]:
    V,err=genuine(np.load(f),n); r=inv(V,n); r['m+2k']=r['m']+2*r['k']; r['Gamma+k']=r['dimGamma']+r['k']
    print(f.split('/')[-1],'level err %.1e'%err,r)
