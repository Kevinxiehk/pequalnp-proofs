import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/hessmix')
from hk import *
from nya import Phi, nullsp, RowS, ColS
ex=examples()
for name in ['ex1','ex2','rc45']:
    B=np.transpose(orth(ex[name]),(0,2,1))   # full row-3 block -> full column-3 block
    Y=np.array([Phi(b).ravel() for b in B]); R=Y@RowS.T; C=Y@ColS.T
    YB=nullsp(R.T)@Y; YB=YB.reshape(-1,5,5)
    j0=3; others=[j for j in range(5) if j!=j0]
    col_const=max(np.abs(X[:,j0]-X[:,j0].mean()).max() for X in YB)
    Gs=[np.einsum('ai,bi->ab',YB[:,i,others],YB[:,i,others]) for i in range(5)]
    gram_dev=max(np.abs(G-Gs[0]).max() for G in Gs)
    q=rank(C@np.eye(5)) - 4 if False else rank(np.array([X.sum(0) for X in YB]))
    D=dcpart(B); D=orth(D) if len(D) else D
    ranks=[rank(D[:,i,others]) if len(D) else 0 for i in range(5)]
    print(name,'(transposed) dimYB=%d q=dim C(YB)=%d d=%d | col %d const dev %.1e | row-Gram independent of i dev %.1e | rank phi_i|D per row:'%(len(YB),q,len(D),j0,col_const,gram_dev),ranks,' bound floor((4-q)/2)=',(4-q)//2)
