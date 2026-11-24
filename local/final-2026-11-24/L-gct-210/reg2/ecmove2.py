# double EC moves: row 3 keeps a 2-dim part U of 1^perp, the complementary 2 directions v1, v2 are placed in rows i1, i2 of {0,1,2}.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, itertools
from t import *
from a1 import embed, defect
from a5 import onb
from a6 import T1
from r5_FO2 import FO2
rg=np.random.default_rng(0)
def rowel(i,v):
    m=np.zeros((4,5),complex); m[i]=v; return m
def col(c,x):
    m=np.zeros((4,5),complex); m[:3,c]=x; return m
E=np.eye(5)
def test(name,Uvecs,moves,N):
    B=[rowel(3,u) for u in Uvecs]+[rowel(i,v) for (i,v) in moves]+list(N); B=np.array(B)
    if np.linalg.matrix_rank(B.reshape(len(B),20))<len(B): print(name,'degenerate'); return
    Bo=onb(B); le=level_err(Bo,ntest=60)
    if le>1e-9: print('%-70s dim %d NOT level (err %.1e)'%(name,len(Bo),le)); return
    T=T1(embed(Bo),rg,npts=120); S=np.linalg.svd(T[:,4,:],compute_uv=False)
    sr=[len(rowpart(Bo,[i])) for i in range(4)]
    print('%-70s dim %d level; srow %s e=%d dim T1 %d dim Omega %d FO2 %s'%(name,len(Bo),sr,int((defect(Bo)>1e-8).sum()),len(T),int((S>1e-8).sum()),FO2(embed(Bo),rg)))
    np.save('ec2_%d.npy'%abs(hash(name)%10**6),Bo)
Ncol4=[col(4,[1,-1,0]),col(4,[1,1,-2])]
Nxy=[col(0,[1,-1,0]),col(3,[1,1,-2])]
# shape A: U = {w_0=w_1=w_2, sum=0} = span(1,1,1,-3,0),(1,1,1,0,-3); V = span(e0-e1, e1-e2)
UA=[np.array([1,1,1,-3,0.]),np.array([1,1,1,0,-3.])]
for (i1,i2) in ((0,0),(0,1),(0,2),(2,2)):
    test('A: N={x e_4}, U={w0=w1=w2}, e_%d(e0-e1), e_%d(e1-e2)'%(i1,i2),UA,[(i1,E[0]-E[1]),(i2,E[1]-E[2])],Ncol4)
    test('A\': same with second move e_%d(e0+e1-2e2)'%i2,UA,[(i1,E[0]-E[1]),(i2,E[0]+E[1]-2*E[2])],Ncol4)
# shape B: U = {w_0=w_1, w_2=w_3, sum=0} = span(1,1,-1,-1,0),(1,1,1,1,-4); V = span(e0-e1, e2-e3)
UB=[np.array([1,1,-1,-1,0.]),np.array([1,1,1,1,-4.])]
for (i1,i2) in ((0,0),(0,1),(0,2),(2,2)):
    test('B: N={x e_4}, U={w0=w1,w2=w3}, e_%d(e0-e1), e_%d(e2-e3)'%(i1,i2),UB,[(i1,E[0]-E[1]),(i2,E[2]-E[3])],Ncol4)
# shape C: N = x e_0, y e_3 ; zero columns 1,2,4 ; U = {w1=w2=w4}
UC=[np.array([3,-1,-1,0,-1.]),np.array([0,-1,-1,3,-1.])]
for (i1,i2) in ((0,0),(0,1),(2,2),(1,2)):
    test('C: N={x e_0,y e_3}, U={w1=w2=w4}, e_%d(e1-e2), e_%d(e2-e4)'%(i1,i2),UC,[(i1,E[1]-E[2]),(i2,E[2]-E[4])],Nxy)
    test('C\': second move e_%d(e1+e2-2e4)'%i2,UC,[(i1,E[1]-E[2]),(i2,E[1]+E[2]-2*E[4])],Nxy)
