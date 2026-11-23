# Sanity of the first-order extension test on the known 7-dim level spaces: L must lie in T_1(L) and in T_1(M) for subspaces M of L.
import sys, itertools, numpy as np
sys.path.insert(0,'/home/claude/work/L-gct-210/chief'); import core
P4=np.array(list(itertools.permutations(range(4))))
def cofs(M):
    out=[]
    for i in range(5):
        for j in range(5):
            A=np.delete(np.delete(M,i,axis=0),j,axis=1); out.append(A[np.arange(4)[None,:],P4].prod(axis=1).sum())
    return np.array(out)
rg=np.random.default_rng(2)
for name,sp in core.SP.items():
    B=np.array([np.array(m,dtype=complex) for m in sp()]); d=len(B)
    for sub in (d,max(d-2,1)):
        Mb=B if sub==d else (rg.normal(size=(sub,d))@B.reshape(d,25)).reshape(sub,5,5)
        rows=[cofs(np.ones((5,5))+np.tensordot(rg.normal(size=sub)+1j*rg.normal(size=sub),Mb,axes=1)) for _ in range(60)]
        A=np.array(rows); s=np.linalg.svd(A,compute_uv=False); rk=int((s>1e-8*s[0]).sum())
        viol=abs(A@B.reshape(d,25).T).max()                       # L inside T_1(M) ?
        print(name,'dim L =',d,' dim M =',sub,' dim T_1(M) =',25-rk,'  max |<C(J+m),t>| over t in L: %.1e'%viol)
