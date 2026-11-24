import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, glob
from t import *
from a1 import embed
from a5 import rref_tol, onb
from a6 import T1
from show import rref
np.set_printoptions(precision=3,suppress=True,linewidth=200)
rg=np.random.default_rng(3)
for f in sys.argv[1:]:
    B0=np.load(f); R=rref_tol(onb(B0),1e-5); B=onb(R)
    T=T1(embed(B),rg)
    # quotient T_1 by M: project out
    Mb=embed(B).reshape(len(B),25)
    Tm=T.reshape(len(T),25)
    # extra directions: orthogonal complement of M inside T_1
    Q,_=np.linalg.qr(Mb.conj().T)   # hermitian projector on conj... simpler: pick T elements, subtract hermitian projection onto span(M)
    Q,_=np.linalg.qr(Mb.T)          # columns span M (as vectors)
    Tx=Tm-(Tm@Q.conj())@Q.T
    u,s,vh=np.linalg.svd(Tx); r=int((s>1e-7).sum()); X=vh[:r]
    print('=====',f,'dim T1',len(T),'extra',r)
    rho=X.reshape(r,5,5)[:,4,:]
    Rr,_=rref(rho.reshape(r,1,5)) if r else (np.zeros((0,1,5)),None)
    print('row-r projection of T1 (rref):'); print(Rr.reshape(-1,5))
    # print extras in rref form
    Xr,_=rref(X.reshape(r,5,5))
    for m in Xr: print(m); print()
