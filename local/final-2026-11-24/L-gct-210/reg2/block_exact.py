# EXACT member of the BLOCK family (NOTES-reg2 14.5): m = (1,0,-2,1,0), a = 1.  Level identity, dim T_1, rank q, and the exact single-row /
# single-column parts (the space is NOT line-spanned).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp
from dr211_special import perm, bigY, fo_matrix, hessian
t,a=[sp.Integer(int(v)) for v in (sys.argv[1:3] if len(sys.argv)>2 else (1,1))]
m=[t,0,-1-t,1,0]
U=[[0,1,0,0,-1],[m[2],0,-m[0],0,m[0]-m[2]],[m[3],0,0,-m[0],m[0]-m[3]]]
B=[]
for w in U:
    b=sp.zeros(4,5); b[0,:]=sp.Matrix([w]); B.append(b)
b=sp.zeros(4,5); b[2,:]=sp.Matrix([m]); B.append(b)
for x in ([0,1,-1,0],[0,0,1,-1]):
    J=[0,x[2]-x[3],x[3]-x[1],x[1]-x[2]]; b=sp.zeros(4,5)
    for i in range(4): b[i,1]=x[i]; b[i,4]=a*J[i]
    B.append(b)
print('t=%s a=%s: level identity:'%(t,a),sp.expand(perm(sp.ones(5,5)+bigY(B))-120)==0)
A=fo_matrix(B); N=A.nullspace(); Nm=sp.Matrix.hstack(*N).T; best=0
for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
    H=hessian(B,yv); best=max(best,(Nm*H*Nm.T).rank())
print('dim T_1 = %d, rank q = %d => every level space containing M has dim <= %d'%(len(N),best,len(N)-(best+1)//2))
# exact single-row / single-column parts of M
Mm=sp.Matrix([[b[i,j] for i in range(4) for j in range(5)] for b in B]).T     # 20 x 6, columns = basis
def part(cells):
    rows=[k for k in range(20) if k not in cells]; C=Mm.extract(rows,list(range(6))).nullspace(); return len(C)
rp=[part([5*i+j for j in range(5)]) for i in range(4)]; cp=[part([5*i+j for i in range(4)]) for j in range(5)]
print('single-row parts',rp,' single-column parts',cp,' (sum',sum(rp)+sum(cp),'< 6: not line-spanned)')
