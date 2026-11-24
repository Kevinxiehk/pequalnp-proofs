import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from ext55 import *
m=int(sys.argv[1]); rg=np.random.default_rng(int(sys.argv[2])); nst=int(sys.argv[3])
for f in sys.argv[4:]:
    B=onb(np.load(f)); Mb=embed(B); T=T1(Mb,rg,npts=100)
    Q,_=np.linalg.qr(Mb.reshape(len(B),25).T); Tm=T.reshape(len(T),25); X=Tm-(Tm@Q.conj())@Q.T
    u,s,vh=np.linalg.svd(X); r=int((s>1e-7).sum()); D=vh[:r].reshape(r,5,5); res=[]
    for trial in range(nst):
        c,L=solve55(Mb,D,m,rg,iters=150); res.append(c)
    res=np.sort(res); print('%s: T1/M dim %d, m=%d: %d starts, found %d, smallest residuals %s'%(f,r,m,nst,int((res<1e-9).sum()),np.array2string(res[:5],precision=2)),flush=True)
