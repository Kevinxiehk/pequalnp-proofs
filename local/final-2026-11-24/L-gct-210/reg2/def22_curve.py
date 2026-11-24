# (2,2|2) row 0 -> 1 skew deformation on its special curves mu = (0,1,0,0) / (0,1,1,1) (t free): generic dim T_1 over Q(t) and gcd of the
# principal 3x3 minors of q on a polynomial kernel basis (NOTES-reg2 16.2).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp, itertools
from dr211_special import perm, bigY, fo_matrix, hessian
t=sp.symbols('t')
def basis(m3,m4):
    S=1+m3+m4; B=[sp.zeros(4,5) for _ in range(6)]
    v1=[0,m3-1,-m3,1,0]; v2=[0,m4-1,-m4,0,1]
    g11=sum(a*a for a in v1); g12=sum(a*b for a,b in zip(v1,v2)); g22=sum(b*b for b in v2)
    J1=[g12*a-g11*b for a,b in zip(v1,v2)]; J2=[g22*a-g12*b for a,b in zip(v1,v2)]
    B[0][0,:]=sp.Matrix([v1]); B[0][1,:]=t*sp.Matrix([J1]); B[1][0,:]=sp.Matrix([v2]); B[1][1,:]=t*sp.Matrix([J2])
    B[2][1,:]=sp.Matrix([[4,-1,-1,-1,-1]]); B[3][1,:]=sp.Matrix([[-S,-S,5-S,5*m3-S,5*m4-S]])
    B[4][0,0]=1; B[4][2,0]=-1; B[5][2,0]=1; B[5][3,0]=-1
    return B
for (m3,m4) in ((0,0),(1,1)):
    B=basis(m3,m4); print('mu=(0,1,%d,%d): level identity'%(m3,m4),sp.expand(perm(sp.ones(5,5)+bigY(B))-120)==0,flush=True)
    A=fo_matrix(B); dm=sp.polys.matrices.DomainMatrix.from_Matrix(A).convert_to(sp.QQ.frac_field(t)); n=25-dm.rank()
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
            if sp.degree(G,t)<=0: break
        if G is not None and sp.degree(G,t)<=0: break
    print('  generic dim T_1 = %d; gcd of principal 3x3 minors: %s'%(n,sp.factor(G)),flush=True)
