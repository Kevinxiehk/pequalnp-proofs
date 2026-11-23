import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/dc5'); sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
import numpy as np
from tst import V, vk
def pi(w): return w - w.mean(1,keepdims=True) - w.mean(0,keepdims=True) + w.mean()
def rk(M,tol=1e-9):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol*s[0]).sum())
def lemA(B, seed=0):
    B=np.array(B); d=len(B); rng=np.random.default_rng(seed)
    x=rng.normal(size=d)+1j*rng.normal(size=d); t=np.einsum('i,iab->ab',x,B)
    At=np.array([pi(t*b) for b in B]).reshape(d,25)
    single=rk(np.vstack([B.reshape(d,25),At]))
    KK=np.array([pi(B[a]*B[b]) for a in range(d) for b in range(a,d)]).reshape(-1,25)
    full=rk(np.vstack([B.reshape(d,25),KK]))
    return d, single, full
if __name__=='__main__':
    v=vk(1)
    print('V x v: d, dim(K+A_tK), dim(K+pi(K*K))', lemA([np.outer(a,v) for a in V]))
    print('W x v:', lemA([np.outer(a,v) for a in V[:3]]))
    for f in sys.argv[1:]: print(f, lemA(np.load(f)))
