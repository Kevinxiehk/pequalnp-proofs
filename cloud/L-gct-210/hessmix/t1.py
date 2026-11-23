import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/hessmix')
from hk import *
ex=examples()
rng=np.random.default_rng(3)
for name,B in ex.items():
    Bo=orth(B); LV=toV(Bo); l=len(Bo)
    c=rng.normal(size=l)+1j*rng.normal(size=l); t=np.einsum('k,kij->ij',c,Bo)
    Ms={k:MkV(t,k) for k in (3,4,5)}
    orthv=max(np.abs(LV@QV@(Ms[k]@LV.T)).max() for k in (3,4,5))
    imgs={k:(Ms[k]@LV.T).T for k in (3,4,5)}
    r3=rank(imgs[3]); r4=rank(imgs[4]); r5=rank(imgs[5])
    s3=rank(np.vstack([LV,imgs[3]])); s34=rank(np.vstack([LV,imgs[3],imgs[4]])); s345=rank(np.vstack([LV,imgs[3],imgs[4],imgs[5]]))
    # full products L.L : span over t in basis
    LL=np.vstack([ (MkV(Bo[i],3)@LV.T).T for i in range(l)])
    LLL=[]
    for i in range(l):
        for j in range(i,l):
            # cubic product via polarisation of M4: M4_{t} is quadratic in t
            pass
    sLL=rank(np.vstack([LV,LL]))
    print(name,'l=%d orth=%.1e  rk M3L=%d M4L=%d M5L=%d | L+M3L=%d  +M4L=%d +M5L=%d | L+L.L=%d  (bound 24-l=%d)'%(l,orthv,r3,r4,r5,s3,s34,s345,sLL,24-l))
