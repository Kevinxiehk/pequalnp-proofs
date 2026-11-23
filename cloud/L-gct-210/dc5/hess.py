import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/dc5'); sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
import numpy as np
from level import Pk_grad
from tst import V, vk
def pi(w): return w - w.mean(-1,keepdims=True) - w.mean(-2,keepdims=True) + w.mean((-1,-2),keepdims=True)
def rk(M,tol=1e-7):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol*s[0]).sum()), s
def hessimg(t, s, k, e=1e-3):
    # Richardson-extrapolated central difference of the gradient (polynomial, so tiny error)
    def g(h): return Pk_grad(np.array([t+h*s, t-h*s]))[1][:,k]
    a=g(e); b=g(e/2)
    d1=(a[0]-a[1])/(2*e); d2=(b[0]-b[1])/(e)
    return pi((4*d2-d1)/3)
def hdims(B, ks, seed=0):
    B=np.array(B,dtype=complex); B=B/np.abs(B).max(); d=len(B); rng=np.random.default_rng(seed)
    x=rng.normal(size=d)+1j*rng.normal(size=d); x/=np.linalg.norm(x); t=np.einsum('i,iab->ab',x,B)
    rows=[B.reshape(d,25)]; out=[]
    for k in ks:
        rows.append(np.array([hessimg(t,b,k) for b in B]).reshape(d,25))
        out.append(rk(np.vstack(rows))[0])
    return d,out
if __name__=='__main__':
    v=vk(1)
    print('Vxv: d, cumulative dim K+H3K+H4K+H5K:', hdims([np.outer(a,v) for a in V],[3,4,5]))
    print('Wxv:', hdims([np.outer(a,v) for a in V[:3]],[3,4,5]))
    for f in sys.argv[1:]: print(f, hdims(np.load(f),[3,4,5]))
