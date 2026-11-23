import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/split')
from core import *
np.set_printoptions(precision=3,suppress=True,linewidth=150)
B=np.load(sys.argv[1]); m=len(B)
Q,_=np.linalg.qr(B.reshape(m,-1).T); Bo=Q.T.reshape(m,5,5)
rng=np.random.default_rng(5); xs=rnd((60,m),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
print('orthonormal residual per k',np.abs(Pk(np.einsum('ri,iab->rab',xs,Bo))).max(0))
for c in range(5):
    OC=[]
    for i in range(4):
        M=np.zeros((5,5),complex); M[i,c]=1; M[4,c]=-1; OC.append(M)
    sv=np.linalg.svd(np.concatenate([B.reshape(m,-1),np.array(OC).reshape(4,-1)]),compute_uv=False)
    print('col',c,'sv of [Y;onecol]',sv.round(5))
c,al,be,g=decomp(B); print('beta max',np.abs(be).max(),' alpha sv',np.linalg.svd(al,compute_uv=False).round(4))
print('DC part sv',np.linalg.svd(g.reshape(m,-1),compute_uv=False).round(4))
