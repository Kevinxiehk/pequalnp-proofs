# EXACT (Fractions) first- and second-order certificate for integer 4x5 level spaces: dim ker A (>= dim T_1), Omega^perp, and
# rank of q_Y on ker A  =>  every 5x5 level space containing M has dim <= dim ker A - ceil(rank/2).
import sys, itertools, random; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2')
from fractions import Fraction as Fr
from exact_T1 import nullspace, cof
from mstar2_fo2 import hess, rankQ
def E(cells):
    m=[[Fr(0)]*5 for _ in range(4)]
    for (i,j,v) in cells: m[i][j]=Fr(v)
    return m
def cert(B,name,npts=300,seed=5):
    random.seed(seed); d=len(B)
    pt=lambda c:[[Fr(1)+sum(c[k]*B[k][i][j] for k in range(d)) if i<4 else Fr(1) for j in range(5)] for i in range(5)]
    rows=[]
    for _ in range(npts):
        M=pt([random.randint(-4,4) for _ in range(d)]); g=cof(M); assert sum(g[20+j] for j in range(5))==120,'not level'
        rows.append(g)
    R,N=nullspace(rows,25); n=len(N)
    rp,perp=nullspace([v[20:] for v in N],5)
    best=0
    for _ in range(3):
        H=hess(pt([random.randint(-3,3) for _ in range(d)]))
        Q=[[sum(N[a][p]*sum(H[p][q]*N[b][q] for q in range(25)) for p in range(25)) for b in range(n)] for a in range(n)]
        best=max(best,rankQ(Q))
    print('%-58s level at %d integer points; dim ker = %d, dim Omega <= %d, Omega^perp contains %s; rank q = %d  =>  dim L <= %d'%(name,npts,n,rp,[[str(x) for x in v] for v in perp],best,n-(best+1)//2))
U12=[E([(3,0,2),(3,1,-1),(3,2,-1)]),E([(3,3,2),(3,1,-1),(3,2,-1)]),E([(3,4,2),(3,1,-1),(3,2,-1)])]     # {sum w=0, w_1=w_2}
EC=E([(2,1,1),(2,2,-1)])
def colv(c,x): return E([(i,c,x[i]) for i in range(3)])
cert(U12+[colv(0,[1,-1,0]),colv(3,[1,1,-2]),EC],'M*_1: x=(1,-1,0), y=(1,1,-2)')
cert(U12+[colv(0,[2,-1,-1]),colv(3,[0,1,-1]),EC],'M*_1: x=(2,-1,-1), y=(0,1,-1)')
cert(U12+[colv(0,[1,2,-3]),colv(3,[5,-4,-1]),EC],'M*_1: x=(1,2,-3), y=(5,-4,-1)')
cert(U12+[colv(4,[1,-1,0]),colv(4,[1,1,-2]),EC],'M*_2: N = {x e_4^T : sum x = 0}')
# Type F parents for comparison (full free row): add e_3(e_1-e_2) instead of e_2(e_1-e_2)
F3=E([(3,1,1),(3,2,-1)])
cert(U12+[colv(4,[1,-1,0]),colv(4,[1,1,-2]),F3],'Type F parent: free row (+) {x e_4^T}')
