# EXACT certificate over Q(omega) for the (3,1|2) member m = (1, w, w^2, 0, 0) (the only isotropic special member, NOTES-reg2 9.7).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp, itertools
from dr211_special import perm, bigY, fo_matrix, hessian, ys
w=sp.Rational(-1,2)+sp.sqrt(-3)/2
m=[sp.Integer(1),w,sp.expand(w**2),sp.Integer(0),sp.Integer(0)]
Z=lambda: sp.zeros(4,5); B=[]
for k in (1,2,3):
    b=Z(); b[0,0]=m[k]; b[0,k]=-1; b[0,4]=1-m[k]; B.append(b)
b=Z()
for j in range(5): b[1,j]=m[j]
B.append(b); b=Z(); b[1,4]=1; b[2,4]=-1; B.append(b); b=Z(); b[2,4]=1; b[3,4]=-1; B.append(b)
A5=sp.ones(5,5)+bigY(B); print('level identity:',sp.expand(perm(A5)-120)==0,flush=True)
A=fo_matrix(B); K=sp.QQ.algebraic_field(sp.sqrt(-3))
dm=sp.polys.matrices.DomainMatrix.from_Matrix(A).convert_to(K)
rk=dm.rank(); print('rank',rk,'dim T_1 =',25-rk,flush=True)
N=dm.nullspace().to_Matrix(); print('kernel',N.shape,' A N^T = 0:',all(sp.simplify(x)==0 for x in (A*N.T)),flush=True)
best=0
for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
    H=hessian(B,yv); Q=(N*H*N.T).applyfunc(sp.expand)
    r=sp.polys.matrices.DomainMatrix.from_Matrix(Q).convert_to(K).rank(); best=max(best,r)
print('rank q =',best,' => every level space containing M has dim <=',N.shape[0]-(best+1)//2)
