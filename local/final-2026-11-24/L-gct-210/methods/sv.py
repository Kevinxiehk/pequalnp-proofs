import numpy as np, sys, itertools, math
n=5
B=np.load(sys.argv[1]); d=B.shape[0]; T=B.reshape(d,n,n)
rs=T.sum(2); cs=T.sum(1)
print('sv [rs|cs]',np.round(np.linalg.svd(np.hstack([rs,cs]),compute_uv=False),9))
G=T-rs[:,:,None]/n-cs[:,None,:]/n+T.sum((1,2))[:,None,None]/n**2
print('sv gamma',np.round(np.linalg.svd(G.reshape(d,-1),compute_uv=False),9))
perms=list(itertools.permutations(range(n)))
def perm(A): return sum(np.prod([A[i,p[i]] for i in range(n)]) for p in perms)
rng=np.random.default_rng(1)
for _ in range(3):
    c=rng.normal(size=d)+1j*rng.normal(size=d)
    t=np.tensordot(c,T,1); print('perm(J+t)-120',abs(perm(np.ones((n,n))+t)-120), 'norm t',np.linalg.norm(t))
