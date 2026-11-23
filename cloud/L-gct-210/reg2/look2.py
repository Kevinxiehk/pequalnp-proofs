import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
import numpy as np, glob
from t import *
from a1 import embed, defect
from a5 import onb
from a6 import T1, E0
from show import rref
np.set_printoptions(precision=3,suppress=True,linewidth=200)
rg=np.random.default_rng(2)
f=sys.argv[1]; B=np.load(f); Bo=onb(B)
print('single-row parts',[len(rowpart(Bo,[i])) for i in range(4)],'single-col',[len(colpart(Bo,[j])) for j in range(5)],'row proj ranks',[rank(Bo[:,i,:]) for i in range(4)],'col proj',[rank(Bo[:,:,j]) for j in range(5)])
print('support pattern of span (max |entry| over basis):'); print((np.abs(Bo).max(0)>1e-8).astype(int))
T=T1(embed(Bo),rg,npts=90)
Mb=embed(Bo).reshape(6,25); Q,_=np.linalg.qr(Mb.T); Tm=T.reshape(len(T),25); Tx=Tm-(Tm@Q.conj())@Q.T
u,s,vh=np.linalg.svd(Tx); r=int((s>1e-7).sum()); X=vh[:r]
Xr,_=rref(X.reshape(r,5,5))
for m in Xr: print(np.array2string(m,precision=3,suppress_small=True)); print()
