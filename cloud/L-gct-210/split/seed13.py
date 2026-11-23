import sys; sys.path.insert(0,'.')
from core import *
from ext2 import ext_space, complement, search, fresh
from rab import info
def abproj_dims(E,S):
    """E: rows basis (m x 25) of extension space; S: current space (k x 5 x 5). Return dims of alpha/beta projections
    of E and of S"""
    c,al,be,g=decomp(E.reshape(-1,5,5)); c2,al2,be2,g2=decomp(S)
    def rk(M,tol=1e-8):
        s=np.linalg.svd(M,compute_uv=False); return int((s>tol*max(1,s[0] if s.size else 1)).sum())
    return dict(EA=rk(al),EB=rk(be),SA=rk(al2),SB=rk(be2),E=len(E))
if __name__=='__main__':
    rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
    L=np.load('d1_ext1.npy'); I=info(L); print('ex2',I)
    Lf=L.reshape(7,-1); Q,_=np.linalg.qr(Lf.T); O=Q.T.reshape(7,5,5)
    D=rde(L,1e-6)['D'][0]
    for trial in range(3):
        c=rnd((2,7),rng); S=np.concatenate([D[None],np.einsum('qk,kij->qij',c,O)])
        print(' L3 info',info(S))
        E=ext_space(S); print('  ',abproj_dims(E,S))
