import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief')
from core import *
from testAB_lib import hat, sub_with_zero, rank, Qf
rng=np.random.default_rng(9)
tot=0; nonzero=0; bad=0
for name,f in SP.items():
    B=f(); Bh=hat(B)
    for r,rp in itertools.combinations(range(5),2):
        abc=[i for i in range(5) if i not in (r,rp)]
        N=sub_with_zero(B,[(i,j) for i in (r,rp) for j in range(5)]); lam=N.shape[1]
        if lam==0: continue
        for T in itertools.combinations(range(5),2):
            Tc=[c for c in range(5) if c not in T]
            U=sub_with_zero(Bh,[(i,j) for i in (r,rp) for j in Tc]); dU=U.shape[1]
            inL=np.abs(U[0,:]).max()<1e-9
            Pi=np.array([[sum(U[k,a]*Bh[k][i,j] for k in range(len(Bh))) for a in range(dU)] for i in (r,rp) for j in T])
            rq=rank(Pi.T@Qf@Pi)
            q0=inL and rq==0
            for _ in range(2):
                c=N@(rng.normal(size=lam)+1j*rng.normal(size=lam)); x=np.tensordot(c,B,1)
                val=abs(perm(x[np.ix_(abc,Tc)])); tot+=1
                if val>1e-9:
                    nonzero+=1
                    if not q0: bad+=1; print('VIOLATION',name,r,rp,T,val)
print('checked',tot,'values; nonzero B_x[T]:',nonzero,' violations of (C2):',bad)
