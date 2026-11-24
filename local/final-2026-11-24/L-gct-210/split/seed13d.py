import sys; sys.path.insert(0,'.')
from seed13 import *
from polish2 import gpolish
import time
rng=np.random.default_rng(0)
L=np.load('d1_ext1.npy'); Lf=L.reshape(len(L),-1); Q,_=np.linalg.qr(Lf.T); O=Q.T.reshape(len(L),5,5)
D=rde(L,1e-6)['D'][0]
c=rnd((2,len(L)),rng); S=np.concatenate([D[None],np.einsum('qk,kij->qij',c,O)])
E=ext_space(S); C=complement(S,E)
def spec(L4):
    Lf4=L4.reshape(4,-1); Q4,_=np.linalg.qr(Lf4.T); O4=Q4.T.reshape(4,5,5); cc,al,be,g=decomp(O4)
    return np.linalg.svd(al,compute_uv=False), np.linalg.svd(be,compute_uv=False)
for s in range(30):
    f,L4,_=search(S,1,starts=1,seed=1000*s+int(sys.argv[1]),tlimit=15,C=C)
    if f<1e-10:
        sa,sb=spec(L4)
        if sa[2]>1e-7:
            print('near sol: res %.1e  sv alpha'%f, sa.round(8),'sv beta',sb.round(8))
            amb=np.eye(25).reshape(25,5,5)
            f2,L5,hist,sv=gpolish(L4,amb,tlimit=60)
            sa2,sb2=spec(L5); print(' after full polish res %.1e fresh %.1e'%(f2,fresh(L5)),'sv alpha',sa2.round(8),'sv beta',sb2.round(8), 'd',rde(L5,1e-6)['d'])
            np.save('L4_near.npy',L5); break
