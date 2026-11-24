import sys; sys.path.insert(0,'.')
from forms import *
Chi=np.array([chi(c) for c in range(5)]).T
Gs=[]
for s in range(40):
    a=rng.normal(size=4)+1j*rng.normal(size=4)
    X=sum(ai*b for ai,b in zip(a,Kb))[:3]
    for k in (4,5): Gs.append((k,Chi.T@Q(X,k)@Chi))
mons={s:[(c,d) for c in range(5) for d in range(c,5) if (c+d)%5==s] for s in range(5)}
for s in range(1,5):
  for k in (4,5,None):
    rows=[[G[c,d]*(1 if c==d else 2) for (c,d) in mons[s]] for kk,G in Gs if (k is None or kk==k)]
    A=np.array(rows); U,sv,Vh=np.linalg.svd(A); r=(sv>1e-8*sv[0]).sum()
    msg='s=%d k=%s monomials %s rank %d'%(s,k,mons[s],r)
    if r<3:
        nv=Vh[r:].conj()  # relation: coefficient vector annihilated
        # annihilator: vectors y with A y = 0 -> Vh[r:] rows conj
        y=Vh[r:].conj().T[:,0]; y=y/y[np.argmax(abs(y))]
        msg+=' kernel '+str(np.round(y,6))
    print(msg)
