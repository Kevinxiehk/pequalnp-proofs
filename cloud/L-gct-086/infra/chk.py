import numpy as np, itertools, sys
def perm(A):
    n=A.shape[0]; s=0
    for p in itertools.permutations(range(n)):
        pr=1
        for i in range(n): pr*=A[i,p[i]]
        s+=pr
    return s
rng=np.random.default_rng(0)
for f in sys.argv[1:]:
    B=np.load(f); d,n,_=B.shape
    flat=B.reshape(d,-1); rk=np.linalg.matrix_rank(flat,tol=1e-8); sv=np.linalg.svd(flat,compute_uv=False)
    errs=[]
    for _ in range(20):
        c=rng.normal(size=d)+1j*rng.normal(size=d); c*=3
        t=np.tensordot(c,B,1); errs.append(abs(perm(np.ones((n,n))+t)-np.math.factorial(n) if hasattr(np,'math') else 0))
    import math
    errs=[abs(perm(np.ones((n,n))+np.tensordot(c,B,1))-math.factorial(n)) for c in [3*(rng.normal(size=d)+1j*rng.normal(size=d)) for _ in range(20)]]
    print(f,'dim',d,'rank',rk,'minsv %.2e'%sv[-1],'max|perm-n!| %.2e'%max(errs),'rowsums %.1e colsums %.1e'%(abs(B.sum(2)).max(),abs(B.sum(1)).max()))
