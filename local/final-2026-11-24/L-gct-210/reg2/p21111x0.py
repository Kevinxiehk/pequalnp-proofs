# (2,1,1|1,1)(a,a) sub-family x = (0,0,1,-1): dim T_1 = 10 generically; rank q >= 3 for all s via gcd of 3x3 minors over Q(s) (as dr211_special S4)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp, itertools
from dr211_special import perm, bigY, fo_matrix, hessian, s
def rowel(i,w): m=sp.zeros(4,5); m[i,:]=sp.Matrix([w]); return m
def colel(c,x): m=sp.zeros(4,5); m[:,c]=sp.Matrix(x); return m
u1=[1,s,-1-s,0,0]; u2=[u1[1]-u1[2],u1[2]-u1[0],u1[0]-u1[1],0,0]; x=[0,0,1,-1]; xp=[0,2,-1,-1]
B=[rowel(0,[-1,-1,-1,4,-1]),rowel(0,[-1,-1,-1,-1,4]),rowel(1,u1),rowel(2,[sp.expand(e) for e in u2]),colel(3,x),colel(4,xp)]
print('level identity:',sp.expand(perm(sp.ones(5,5)+bigY(B))-120)==0,flush=True)
A=fo_matrix(B); dm=sp.polys.matrices.DomainMatrix.from_Matrix(A).convert_to(sp.QQ.frac_field(s)); print('generic dim T_1 =',25-dm.rank(),flush=True)
N=dm.nullspace().to_Matrix(); rows=[]
for r in range(N.shape[0]):
    row=[sp.together(e) for e in N.row(r)]; den=sp.lcm([sp.denom(e) for e in row]); rows.append([sp.expand(sp.cancel(e*den)) for e in row])
N=sp.Matrix(rows); G=None
for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
    H=hessian(B,yv); Q=sp.expand(N*H*N.T)
    for idx in itertools.combinations(range(N.shape[0]),3):
        d=sp.expand(Q.extract(list(idx),list(idx)).det(method='berkowitz'))
        if d==0: continue
        G=d if G is None else sp.gcd(G,d)
        if sp.degree(G,s)<=0: break
    print('y=%s gcd of principal 3x3 minors: %s'%(str(yv),sp.factor(G)),flush=True)
    if sp.degree(G,s)<=0: break
