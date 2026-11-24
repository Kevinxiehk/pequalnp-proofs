# EXACT check of the RANK-ONE shape (NOTES-reg2 14.3): m = (1,0,w^2,0,w), U = {1,m}^perp (row 0), e_2 m^T, (0,1,-2,1) e_3^T,
# (e_3 - e_1) (x) (m o m).  Level identity, dim T_1, rank q, single-row / single-column parts (over Q(sqrt -3)).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp
from dr211_special import perm, bigY, fo_matrix, hessian
w=sp.Rational(-1,2)+sp.sqrt(-3)/2; w2=sp.expand(w**2)
m=[1,0,w2,0,w]; mm=[sp.expand(x*x) for x in m]
Um=sp.Matrix([[1]*5,m]).nullspace()
B=[]
for v in Um:
    b=sp.zeros(4,5); b[0,:]=v.T.applyfunc(sp.expand); B.append(b)
b=sp.zeros(4,5); b[2,:]=sp.Matrix([m]); B.append(b)
b=sp.zeros(4,5); b[:,3]=sp.Matrix([0,1,-2,1]); B.append(b)
b=sp.zeros(4,5); b[1,:]=-sp.Matrix([mm]); b[3,:]=sp.Matrix([mm]); B.append(b)
L=sp.expand(perm(sp.ones(5,5)+bigY(B))-120); P=sp.Poly(L,*sp.symbols('y1:7'))
print('level identity:', all(sp.simplify(c)==0 for c in P.coeffs()))
K=sp.QQ.algebraic_field(sp.sqrt(-3))
A=fo_matrix(B); dm=sp.polys.matrices.DomainMatrix.from_Matrix(A).convert_to(K); n=25-dm.rank(); N=dm.nullspace().to_Matrix(); best=0
for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
    H=hessian(B,yv); best=max(best,sp.polys.matrices.DomainMatrix.from_Matrix((N*H*N.T).applyfunc(sp.expand)).convert_to(K).rank())
print('dim T_1 = %d, rank q = %d => bound %d'%(n,best,n-(best+1)//2))
Mm=sp.Matrix([[b[i,j] for i in range(4) for j in range(5)] for b in B]).T
def part(cells):
    rows=[k for k in range(20) if k not in cells]
    return 6-sp.polys.matrices.DomainMatrix.from_Matrix(Mm.extract(rows,list(range(6)))).convert_to(K).rank()
print('single-row parts',[part([5*i+j for j in range(5)]) for i in range(4)],' single-column parts',[part([5*i+j for i in range(4)]) for j in range(5)])
