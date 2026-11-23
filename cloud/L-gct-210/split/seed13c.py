import sys; sys.path.insert(0,'.')
from seed13 import *
import time
rng=np.random.default_rng(int(sys.argv[1]))
L=np.load(sys.argv[2]); Lf=L.reshape(len(L),-1); Q,_=np.linalg.qr(Lf.T); O=Q.T.reshape(len(L),5,5)
D=rde(L,1e-6)['D'][0]
c=rnd((2,len(L)),rng); S=np.concatenate([D[None],np.einsum('qk,kij->qij',c,O)])
E=ext_space(S); C=complement(S,E)
best=(0,None); t0=time.time()
for s in range(60):
    f,L4,_=search(S,1,starts=1,seed=1000*s+7,tlimit=15,C=C)
    if f<1e-10:
        x=L4[3].reshape(-1); y=x-Q@(Q.conj().T@x); dist=np.linalg.norm(y)/np.linalg.norm(x)
        if dist>best[0]: best=(dist,L4)
    if time.time()-t0>float(sys.argv[3]): break
dist,L4=best; print('best dist from ex2 span %.3e'%dist)
if L4 is not None:
    np.save('L4_13.npy',L4)
    Lf4=L4.reshape(4,-1); Q4,_=np.linalg.qr(Lf4.T); O4=Q4.T.reshape(4,5,5); cc,al,be,g=decomp(O4)
    print('fresh %.1e'%fresh(L4),'sv alpha',np.linalg.svd(al,compute_uv=False).round(6),'sv beta',np.linalg.svd(be,compute_uv=False).round(6))
    print('E dim of L4',len(ext_space(L4)))
