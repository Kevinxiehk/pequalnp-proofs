import numpy as np, sys, glob
sys.path.insert(0,'.'); sys.path.insert(0,'../methods')
from core import *
import spaces
def load(f):
    a=np.load(f); return a.reshape(len(a),25)
def prods(A,B):
    return np.array([prod(a,b)[0] for a in A for b in B])
def closure(Lu,maxit=6):
    S=orth(Lu,1e-9); dims=[len(S)]
    for it in range(maxit):
        S2=orth(np.vstack([S,prods(S,S)]),1e-8)
        dims.append(len(S2))
        if len(S2)==len(S): break
        S=S2
    return S,dims
def qinfo(S):
    C=to_coords(S); Gm=C@QM@C.T
    s=np.linalg.svd(Gm,compute_uv=False); r=int((s>1e-8*s[0]).sum())
    k=len(S); return r, k-r, (k-r)+ (r//2)  # rank, radical, max iso dim
def examples():
  S={}
  for k in ['ex1','ex2','L080','rank1weight']: S[k]=spaces.SP[k]()
  S['rc45p1']=load('../split/rc45p1.npy'); S['weight6']=load('../dc5/weight6_p23.npy'); S['k4gen']=load('../dc5/k4gen.npy')
  S['p23supp1']=load('../lowd/p23supp_7_23_142_1.npy'); S['p23gen0']=load('../lowd/p23gen_7_23_122_0.npy')
  return S
if __name__=='__main__':
 S=examples()
 for k,B in S.items():
    B=B-B.mean(1,keepdims=True); Lu=orth(Phi(B))
    W,dims=closure(Lu)
    W1=orth(np.vstack([Lu,prods(Lu,Lu)]),1e-8)
    print('%-10s growth chain %s ; Q on L+L∘L: rank,rad,maxiso=%s ; on closure: %s'%(k,dims,qinfo(W1),qinfo(W)))
