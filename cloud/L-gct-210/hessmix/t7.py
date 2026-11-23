# max common isotropic subspace containing delta for forms Q,H3_delta,H4_delta,H5_delta (quadratic conditions at delta only)
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/hessmix')
from hk import *
from scipy.optimize import least_squares
rng=np.random.default_rng(int(sys.argv[2]) if len(sys.argv)>2 else 0)
ex=examples()
name=sys.argv[1]; m=int(sys.argv[3])
D=orth(dcpart(orth(ex[name])))
dl=D[0] if len(D)==1 else np.einsum('k,kij->ij',rng.normal(size=len(D)),D)
dv=toV(dl[None])[0]
forms=[QV]+[VB@hess_full(dl,k)@VB.T for k in (3,4,5)]
forms=[F/np.linalg.norm(F) for F in forms]
# unknown: m-1 vectors in V (complex) ; L = span(dv, X)
def unpack(z):
    z=z[:len(z)//2]+1j*z[len(z)//2:]; return z.reshape(m-1,24)
def res(z):
    X=unpack(z); Bm=np.vstack([dv,X])
    Bo=np.linalg.qr(Bm.T)[0].T  # orthonormal-ish (complex QR on columns)
    out=[]
    for F in forms:
        R=Bo@F@Bo.T; iu=np.triu_indices(m); out.append(R[iu])
    o=np.concatenate(out); return np.concatenate([o.real,o.imag])
best=None
for trial in range(6):
    z0=rng.normal(size=2*(m-1)*24)
    r=least_squares(res,z0,method='trf',max_nfev=300)
    X=unpack(r.x); Bm=np.vstack([dv,X]); s=sv(Bm)
    nr=np.linalg.norm(r.fun)
    # r,d of the span
    B=fromV(np.linalg.svd(Bm)[2][:m])
    print(name,'m=',m,'trial',trial,'res %.2e'%nr,'min sv %.2e'%s[-1], inv(B) if nr<1e-8 else '')
    sys.stdout.flush()
