import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/hessmix')
from hk import *
rng=np.random.default_rng(21)
def Wdim(Bo):
    l=len(Bo); LV=toV(Bo); c=rng.normal(size=(150,l))+1j*rng.normal(size=(150,l)); c/=np.linalg.norm(c,axis=1,keepdims=True)
    P,G=Pk_grad(np.einsum('rk,kij->rij',c,Bo)); rows=G[:,2:6].reshape(-1,25)@VB.T
    s=sv(rows); return int((s>1e-8*s[0]).sum())   # = dim W = 24 - dim E
ex=examples()
for name,B in ex.items():
    Bo=orth(B); l=len(Bo); out=[]
    for m in range(1,l+1):
        ws=[]
        for _ in range(2):
            C=rng.normal(size=(m,l))+1j*rng.normal(size=(m,l)); S=orth(np.einsum('mk,kij->mij',C,Bo)); ws.append(Wdim(S))
        out.append('%d:%d(2m+2=%d)'%(m,min(ws),2*m+2))
    print(name,' '.join(out))
