import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/dc5'); sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
import numpy as np
from level import Pk
def pi(w): return w - w.mean(-1,keepdims=True) - w.mean(-2,keepdims=True) + w.mean((-1,-2),keepdims=True)
def weight_dc(sig,tau,N,E):
    P=np.zeros((25,25))
    for i in range(5):
        for j in range(5): P[i*5+j, sig[i]*5+tau[j]]=1
    z=np.exp(2j*np.pi/N); B=[]
    for e in E:
        u,s,vh=np.linalg.svd(P-z**e*np.eye(25)); ns=vh[s<1e-9].conj().reshape(-1,5,5)
        if len(ns)==0: continue
        D=pi(ns).reshape(len(ns),25)           # DC parts (pi commutes with the symmetry)
        uu,ss,vv=np.linalg.svd(D); r=int((ss>1e-9).sum())
        if r: B+=list(vv[:r].reshape(-1,5,5))
    return np.array(B)
if __name__=='__main__':
    B=weight_dc([1,2,3,4,0],[1,2,0,4,3],30,range(1,10))
    d=len(B); print('dim',d)
    G=np.einsum('aij,bij->ab',B,B); C=np.einsum('aij,bij,cij->abc',B,B,B)
    print('max |p2 polar|',np.abs(G).max(),' max |p3 polar|',np.abs(C).max())
    rng=np.random.default_rng(0); w=np.zeros(6)
    for _ in range(5):
        x=rng.normal(size=d)+1j*rng.normal(size=d); t=np.einsum('i,iab->ab',x,B); w=np.maximum(w,np.abs(Pk(t)[0]))
    print('max |P_k| k=0..5',np.round(w,8)); print('row/col sums',np.abs(B.sum(2)).max(),np.abs(B.sum(1)).max())
    np.save('weight6_p23.npy',B)
