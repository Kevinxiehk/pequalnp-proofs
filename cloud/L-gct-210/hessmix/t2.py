import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/hessmix')
from hk import *
ex=examples()
rng=np.random.default_rng(5)
for name,B in ex.items():
    Bo=orth(B); LV=toV(Bo); l=len(Bo)
    D=dcpart(Bo)
    if len(D)==0: continue
    D=orth(D); d=len(D)
    c=rng.normal(size=d)+1j*rng.normal(size=d); t=np.einsum('k,kij->ij',c,D)
    Ms={k:MkV(t,k) for k in (3,4,5)}
    imgs={k:(Ms[k]@LV.T).T for k in (3,4,5)}
    orthv=max(np.abs(LV@QV@imgs[k].T).max() for k in (3,4,5))
    r=[rank(imgs[k]) for k in (3,4,5)]
    s3=rank(np.vstack([LV,imgs[3]])); s34=rank(np.vstack([LV,imgs[3],imgs[4]])); s345=rank(np.vstack([LV,imgs[3],imgs[4],imgs[5]]))
    # all delta in D
    allimg=np.vstack([ (MkV(D[i],3)@LV.T).T for i in range(d)])
    sD3=rank(np.vstack([LV,allimg]))
    print(name,inv(B),'at delta in D: rk M3L,M4L,M5L=',r,' L+M3=%d +M4=%d +M5=%d ; L+M3_D L=%d (24-l=%d) orth %.1e'%(s3,s34,s345,sD3,24-l,orthv))
    # check H3 formula: H3_delta(s,s') = 4 sum delta u u'
    s=rng.normal(size=(5,5)); s-=s.mean(); s2=rng.normal(size=(5,5)); s2-=s2.mean()
    def Phi(x):
        m,a_,b_,g=parts(x); return g-1.5*ab(a_,b_)
    H=hess_full(t,3)
    print('   H3 formula check', abs(s.ravel()@H@s2.ravel()-4*(t*Phi(s)*Phi(s2)).sum()))
