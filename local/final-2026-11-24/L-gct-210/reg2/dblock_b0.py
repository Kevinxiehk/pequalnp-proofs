# DOUBLE-BLOCK family on the line b = 0 (NOTES-reg2 14.8): generic dim T_1 and gcd of 3x3 / 5x5 principal minors of q over Q(a).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp, itertools
from dr211_special import perm, bigY, fo_matrix, hessian
a=sp.symbols('a')
B=[]
for u in ([3,0,-1,-1,-1],[0,3,-1,-1,-1]):
    m=sp.zeros(4,5); m[0,:]=sp.Matrix([u]); B.append(m)
for x in ([0,1,-1,0],[0,0,1,-1]):
    J=[0,x[2]-x[3],x[3]-x[1],x[1]-x[2]]; m=sp.zeros(4,5)
    for i in range(4): m[i,0]=x[i]; m[i,1]=a*J[i]
    B.append(m)
for w in ([-1,1,0],[0,-1,1]):
    m=sp.zeros(4,5)
    for j in range(3): m[2,2+j]=w[j]
    B.append(m)
A=fo_matrix(B); dm=sp.polys.matrices.DomainMatrix.from_Matrix(A).convert_to(sp.QQ.frac_field(a)); n=25-dm.rank(); print('b=0: generic dim T_1 =',n,flush=True)
N=dm.nullspace().to_Matrix(); rows=[]
for r in range(N.shape[0]):
    row=[sp.together(e) for e in N.row(r)]; den=sp.lcm([sp.denom(e) for e in row]); rows.append([sp.expand(sp.cancel(e*den)) for e in row])
N=sp.Matrix(rows); need=2*(n-8)-1     # bound <= 8 needs rank >= 2(n-8)-1
print('rank needed:',need,flush=True)
G=None
for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
    H=hessian(B,yv); Q=sp.expand(N*H*N.T)
    for idx in itertools.combinations(range(N.shape[0]),need):
        d=sp.expand(Q.extract(list(idx),list(idx)).det(method='berkowitz'))
        if d==0: continue
        G=d if G is None else sp.gcd(G,d)
        if sp.degree(G,a)<=0: break
    print('gcd of principal %dx%d minors: %s'%(need,need,sp.factor(G)),flush=True)
    if G is not None and sp.degree(G,a)<=0: break
