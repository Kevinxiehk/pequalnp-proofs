import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/split')
from core import *
np.set_printoptions(precision=3,suppress=True,linewidth=160)
for f in sys.argv[1:]:
    B=np.load(f); g=B[0]; g=g/np.abs(g).max()
    print(f); print('g=\n',g)
    print(' row sq',(g*g).sum(1),' row cube',(g**3).sum(1))
    print(' col sq',(g*g).sum(0),' col cube',(g**3).sum(0))
    print(' g g^T=\n',g@g.T); print(' g^T g=\n',g.T@g)
    c,al,be,gg=decomp(B)
    print(' alpha sv',np.linalg.svd(al,compute_uv=False).round(4),' beta sv',np.linalg.svd(be,compute_uv=False).round(4))
