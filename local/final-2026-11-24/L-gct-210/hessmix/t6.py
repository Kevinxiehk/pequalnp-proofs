import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/hessmix')
from hk import *
ex=examples()
rng=np.random.default_rng(17)
def Edim(Bo,npts=200):
    l=len(Bo); c=rng.normal(size=(npts,l))+1j*rng.normal(size=(npts,l))
    c/=np.linalg.norm(c,axis=1,keepdims=True)
    T=np.einsum('rk,kij->rij',c,Bo)
    P,G=Pk_grad(T)
    rows=G[:,2:6].reshape(-1,25)@VB.T
    s=sv(rows); r=int((s>1e-8*s[0]).sum())
    return 24-r, s[max(r-2,0):r+2]
for name,B in ex.items():
    Bo=orth(B); e,s=Edim(Bo)
    print(name,len(Bo),'dim E(L) in V =',e,' sv around cut',s)
