import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/chief')
from core import *
def hat(B): return np.concatenate([np.ones((1,5,5),complex),B])
def sub_with_zero(Bh,cells):
    A=np.array([[Bh[k][i,j] for k in range(len(Bh))] for (i,j) in cells]); return nullspace(A)
def rank(A,tol=1e-8):
    A=np.atleast_2d(A)
    if A.size==0: return 0
    s=np.linalg.svd(A,compute_uv=False); return int(np.sum(s>tol*max(1,s[0])))
Qf=np.array([[0,0,0,1],[0,0,1,0],[0,1,0,0],[1,0,0,0]],complex)
def thmB(B,rng,verbose=False):
    Bh=hat(B); stats={}; viol=[]
    for r,rp in itertools.combinations(range(5),2):
        abc=[i for i in range(5) if i not in (r,rp)]
        for T in itertools.combinations(range(5),2):
            Tc=[c for c in range(5) if c not in T]
            U=sub_with_zero(Bh,[(i,j) for i in (r,rp) for j in Tc]); dU=U.shape[1]
            if dU==0: continue
            inL=np.abs(U[0,:]).max()<1e-9
            Pi=np.array([[sum(U[k,a]*Bh[k][i,j] for k in range(len(Bh))) for a in range(dU)] for i in (r,rp) for j in T])
            dPi=rank(Pi); rq=rank(Pi.T@Qf@Pi)
            fz=True
            for _ in range(4):
                c=U@(rng.normal(size=dU)+1j*rng.normal(size=dU)); u=np.tensordot(c,Bh,1)
                if abs(perm(u[np.ix_(abc,Tc)]))>1e-8: fz=False
            if not inL: typ='B1' if rq<=1 else 'VIOL'
            else: typ='q0' if rq==0 else ('B2' if fz else 'VIOL')
            if typ=='VIOL': viol.append((r,rp,T,dU,dPi,rq,inL,fz))
            stats[(typ,dU,dPi,rq)]=stats.get((typ,dU,dPi,rq),0)+1
    return stats,viol
if __name__=='__main__':
    rng=np.random.default_rng(7)
    s,v=thmB(L9(),rng); print('L9 (P2P3 only, NOT level): stats',s); print('violations',len(v),v[:5])
    # perturbed level space: ex1 with one basis vector perturbed (not level) -> expect violations
    B=ex1().copy(); B[0]=B[0]+0.3*E(4,0)-0.3*E(4,1)
    s,v=thmB(B,rng); print('ex1 perturbed: violations',len(v))
