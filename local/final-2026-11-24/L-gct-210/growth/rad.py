import numpy as np, sys
sys.path.insert(0,'.')
from closure import *
def radical(S):
    C=to_coords(S); Gm=C@QM@C.T
    u,s,vh=np.linalg.svd(Gm); r=int((s>1e-8*s[0]).sum())
    return to_mat(vh[r:].conj()@C)
if __name__=='__main__':
 S=examples()
 for k,B in S.items():
    B=B-B.mean(1,keepdims=True); Lu=orth(Phi(B))
    S1=orth(np.vstack([Lu,prods(Lu,Lu)]),1e-8)
    R=orth(radical(S1))
    q,t=checkP23(R)
    print('%-10s dim(L+L∘L)=%d  radical dim %d  |Q| %.1e |T| %.1e  growth of radical %s'%(k,len(S1),len(R),q,t,growth(R,1e-7)))
