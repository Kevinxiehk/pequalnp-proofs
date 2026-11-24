# Second-generator certificates (NOTES-reg2 14.11) for one-parameter (3,10,8) curves: generic dim T_1 over Q(p) (sympy, full FO matrix) and gcd of
# the principal 3x3 minors of q_Y on a polynomial kernel basis; independent of the lift/Gram method used before.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp, itertools
from dr211_special import perm, bigY, fo_matrix, hessian
p=sp.symbols('p')
def rowel(i,w): m=sp.zeros(4,5); m[i,:]=sp.Matrix([w]); return m
def colel(c,x): m=sp.zeros(4,5); m[:,c]=sp.Matrix(x); return m
def run(name,B):
    print(name,'level identity:',sp.expand(perm(sp.ones(5,5)+bigY(B))-120)==0,flush=True)
    A=fo_matrix(B); dm=sp.polys.matrices.DomainMatrix.from_Matrix(A).convert_to(sp.QQ.frac_field(p)); n=25-dm.rank()
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
            if sp.degree(G,p)<=0: break
        if G is not None and sp.degree(G,p)<=0: break
    print('  generic dim T_1 = %d; gcd of principal 3x3 minors of q on ker A(p): %s'%(n,sp.factor(G)),flush=True)
which=sys.argv[1]
if which=='BB':
    x=[1,0,p,-1-p]; xp=[x[2]-x[3],0,x[3]-x[0],x[0]-x[2]]
    run('(2,2|1,1)BB',[rowel(0,[1,-1,0,0,0]),rowel(0,[1,0,-1,0,0]),rowel(1,[-1,-1,-1,4,-1]),rowel(1,[-1,-1,-1,-1,4]),colel(3,x),colel(4,xp)])
if which=='BBpts':
    for pv in (1,-1):
        x=[1,0,pv,-1-pv]; xp=[x[2]-x[3],0,x[3]-x[0],x[0]-x[2]]
        B=[rowel(0,[1,-1,0,0,0]),rowel(0,[1,0,-1,0,0]),rowel(1,[-1,-1,-1,4,-1]),rowel(1,[-1,-1,-1,-1,4]),colel(3,x),colel(4,xp)]
        A=fo_matrix(B); N=A.nullspace(); Nm=sp.Matrix.hstack(*N).T; best=0
        for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
            H=hessian(B,yv); best=max(best,(Nm*H*Nm.T).rank())
        print('BB p=%d: dim T_1 = %d, rank q = %d => bound %d'%(pv,len(N),best,len(N)-(best+1)//2),flush=True)
