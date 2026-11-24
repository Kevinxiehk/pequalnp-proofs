import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/split')
from core import *
z=np.exp(2j*np.pi/5); rng=np.random.default_rng(0)
def nullsp(vs):  # vectors x with x . v = 0 for v in vs (bilinear)
    A=np.array(vs); u,s,vh=np.linalg.svd(A); return vh[len(vs):]   # rows, orth wrt hermitian -> fix below
for a in range(1,5):
  for b in range(1,5):
    v=z**(a*np.arange(5)); vp=z**(b*np.arange(5))
    # x with x.vp = 0 (bilinear): null space of vp^T
    X=np.linalg.svd(vp[None,:])[2][1:].conj()  # hermitian null of vp -> need bilinear: use conj trick
    X=np.linalg.svd(vp[None,:].conj())[2][1:]  # rows y with sum vp_i y_i ... check
    X=np.array([x for x in X]); assert np.abs(X@vp).max()<1e-12
    Z=np.linalg.svd(v[None,:].conj())[2][1:]; assert np.abs(Z@v).max()<1e-12
    B=[np.outer(x,v) for x in X]+[np.outer(vp,zz) for zz in Z]
    B=np.array(B); r,_=span_info(B,1e-9)
    xs=rnd((40,len(B)),rng); T=np.einsum('ri,iab->rab',xs,B); P=Pk(T)
    print(a,b,'dim',r,' max|P_k| k=1..5:',np.abs(P[:,1:]).max(0).round(10))
