import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/hessmix')
from hk import *
ex=examples()
rng=np.random.default_rng(13)
def prodspace(Bo,ks,npts=None):
    LV=toV(Bo); l=len(Bo)
    rows=[]
    # M_t for t in a set of points spanning; M4_t quadratic in t, M5 cubic: use random points
    npts = npts or {3:l,4:l*(l+1)//2+2,5:l*(l+1)*(l+2)//6+3}
    for k in ks:
        for q in range(npts[k] if isinstance(npts,dict) else npts):
            if k==3 and q<l: t=Bo[q]
            else:
                c=rng.normal(size=l)+1j*rng.normal(size=l); t=np.einsum('k,kij->ij',c,Bo)
            rows.append((MkV(t,k)@LV.T).T)
    return LV,np.vstack(rows)
for name,B in ex.items():
    Bo=orth(B); l=len(Bo)
    for ks in [(3,),(3,4),(3,4,5)]:
        LV,X=prodspace(Bo,ks)
        Xo=np.linalg.svd(X)[2][:rank(X)]
        G=Xo.conj()@QV@Xo.T  # bilinear (not hermitian) -> use Xo rows as basis: Gram = Xo QV Xo^T
        G=Xo@QV@Xo.T
        print(name,'l=%d'%l,ks,'dim X=%d rank Q|X=%d  dim(L+X)=%d   bound 24-2l=%d, 24-l=%d'%(len(Xo),rank(G,1e-7),rank(np.vstack([LV,X])),24-2*l,24-l),
              ' L.X orth %.1e'%np.abs(LV@QV@Xo.T).max())
