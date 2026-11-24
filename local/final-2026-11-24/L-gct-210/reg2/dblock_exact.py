# EXACT member of the DOUBLE-BLOCK family (NOTES-reg2 14.8): level identity, dim T_1, rank q, single-row/column parts, Omega.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp
from dr211_special import perm, bigY, fo_matrix, hessian
a,b=[sp.Rational(v) for v in (sys.argv[1:3] if len(sys.argv)>2 else ('1','1'))]
B=[]
for u in ([3,0,-1,-1,-1],[0,3,-1,-1,-1]):
    m=sp.zeros(4,5); m[0,:]=sp.Matrix([u]); B.append(m)
for x in ([0,1,-1,0],[0,0,1,-1]):
    J=[0,x[2]-x[3],x[3]-x[1],x[1]-x[2]]; m=sp.zeros(4,5)
    for i in range(4): m[i,0]=x[i]; m[i,1]=a*J[i]
    B.append(m)
for w in ([-1,1,0],[0,-1,1]):
    J=[w[1]-w[2],w[2]-w[0],w[0]-w[1]]; m=sp.zeros(4,5)
    for j in range(3): m[2,2+j]=w[j]; m[3,2+j]=b*J[j]
    B.append(m)
print('a=%s b=%s level identity:'%(a,b),sp.expand(perm(sp.ones(5,5)+bigY(B))-120)==0)
A=fo_matrix(B); N=A.nullspace(); Nm=sp.Matrix.hstack(*N).T; best=0
for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
    H=hessian(B,yv); best=max(best,(Nm*H*Nm.T).rank())
print('dim T_1 = %d, rank q = %d => bound %d; Omega (row-4 parts) rank %d'%(len(N),best,len(N)-(best+1)//2,Nm[:,20:].rank()))
print('Omega basis:',[list(v) for v in Nm[:,20:].T.columnspace()] if False else Nm[:,20:].rref()[0][:Nm[:,20:].rank(),:].tolist())
Mm=sp.Matrix([[m[i,j] for i in range(4) for j in range(5)] for m in B]).T
def part(cells):
    rows=[k for k in range(20) if k not in cells]; return len(Mm.extract(rows,list(range(6))).nullspace())
print('single-row parts',[part([5*i+j for j in range(5)]) for i in range(4)],' single-column parts',[part([5*i+j for i in range(4)]) for j in range(5)])
