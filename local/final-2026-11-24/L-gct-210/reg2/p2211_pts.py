# exact certificates (sympy over Q) for (2,2|1,1) BB at p = -1/2 and at x = (0,0,1,-1), and for the 8 leftover BD points.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp
from dr211_special import perm, bigY, fo_matrix, hessian
def rowel(i,w): m=sp.zeros(4,5); m[i,:]=sp.Matrix([w]); return m
def colel(c,x): m=sp.zeros(4,5); m[:,c]=sp.Matrix(x); return m
def cert(B,name,fo2=True):
    lev=sp.expand(perm(sp.ones(5,5)+bigY(B))-120)==0
    A=fo_matrix(B); N=A.nullspace(); n=len(N); best=None
    if fo2:
        Nm=sp.Matrix.hstack(*N).T; best=0
        for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
            H=hessian(B,yv); best=max(best,(Nm*H*Nm.T).rank())
    print('%-34s level %s dim T_1 = %d%s'%(name,lev,n,'' if best is None else ', rank q = %d => bound %d'%(best,n-(best+1)//2)),flush=True)
U0=[rowel(0,[1,-1,0,0,0]),rowel(0,[1,0,-1,0,0])]; U1=[rowel(1,[-1,-1,-1,4,-1]),rowel(1,[-1,-1,-1,-1,4])]
for x in ([] if len(sys.argv)>1 else [[1,0,sp.Rational(-1,2),sp.Rational(-1,2)],[0,0,1,-1]]):
    xp=[x[2]-x[3],0,x[3]-x[0],x[0]-x[2]]
    cert(U0+U1+[colel(3,x),colel(4,xp)],'(2,2|1,1)BB x=%s'%x)
if len(sys.argv)>1:
    for (a,b) in [(-1,1),(-3,1),(1,1),(1,-3),(sp.Rational(-1,3),sp.Rational(-1,3)),(0,-1),(1,-1),(-1,-1)]:
        v=[1,a,b,0,-1-a-b]
        W=sp.Matrix([[1,1,1,1,1],[0,0,0,1,0],v]).nullspace()
        B=[rowel(0,list(w)) for w in W]+[rowel(1,[-1,-1,-1,4,-1]),rowel(1,v),colel(3,[2,0,-1,-1]),colel(4,[0,0,1,-1])]
        cert(B,'(2,2|1,1)BD v=%s'%v,fo2=True)
