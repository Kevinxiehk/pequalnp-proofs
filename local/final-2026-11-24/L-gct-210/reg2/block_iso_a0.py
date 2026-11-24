import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp
from dr211_special import perm, bigY, fo_matrix, hessian
w=sp.Rational(-1,2)+sp.sqrt(-3)/2; t=w; a=0
m=[t,0,sp.expand(-1-t),1,0]; U=[[0,1,0,0,-1],[m[2],0,-m[0],0,sp.expand(m[0]-m[2])],[m[3],0,0,-m[0],sp.expand(m[0]-m[3])]]
B=[]
for u in U:
    b=sp.zeros(4,5); b[0,:]=sp.Matrix([u]); B.append(b)
b=sp.zeros(4,5); b[2,:]=sp.Matrix([m]); B.append(b)
for x in ([0,1,-1,0],[0,0,1,-1]):
    J=[0,x[2]-x[3],x[3]-x[1],x[1]-x[2]]; b=sp.zeros(4,5)
    for i in range(4): b[i,1]=x[i]; b[i,4]=a*J[i]
    B.append(b)
K=sp.QQ.algebraic_field(sp.sqrt(-3))
A=fo_matrix(B); dm=sp.polys.matrices.DomainMatrix.from_Matrix(A).convert_to(K); n=25-dm.rank(); N=dm.nullspace().to_Matrix(); best=0
for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
    H=hessian(B,yv); best=max(best,sp.polys.matrices.DomainMatrix.from_Matrix((N*H*N.T).applyfunc(sp.expand)).convert_to(K).rank())
print('BLOCK t=omega a=0: dim T_1 =',n,'rank q =',best,'bound',n-(best+1)//2)
