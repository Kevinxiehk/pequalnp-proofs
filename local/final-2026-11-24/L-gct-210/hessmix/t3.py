import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/hessmix')
from hk import *
ex=examples()
rng=np.random.default_rng(7)
def excess(LV,t,ks=(3,)):
    imgs=[(MkV(t,k)@LV.T).T for k in ks]
    return rank(np.vstack([LV]+imgs))-len(LV)
for name,B in ex.items():
    Bo=orth(B); l=len(Bo)
    out=[]
    for m in range(2,l+1):
        ex3=[];ex34=[];ex345=[]
        for trial in range(3):
            C=rng.normal(size=(m,l))+1j*rng.normal(size=(m,l))
            S=orth(np.einsum('mk,kij->mij',C,Bo)); SV=toV(S)
            c=rng.normal(size=m)+1j*rng.normal(size=m); t=np.einsum('k,kij->ij',c,S)
            ex3.append(excess(SV,t)); ex34.append(excess(SV,t,(3,4))); ex345.append(excess(SV,t,(3,4,5)))
        out.append('m%d:%s/%s/%s'%(m,min(ex3),min(ex34),min(ex345)))
    print(name,l,' '.join(out))
