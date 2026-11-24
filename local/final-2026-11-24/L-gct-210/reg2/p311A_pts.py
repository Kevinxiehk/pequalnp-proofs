# exact certificates over Q(sqrt -3) at sample members of (3,1|1,1) case A (x = (0,1,p,-1-p) and the point x = (0,0,1,-1)).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp
from dr211_special import perm, bigY, fo_matrix, hessian
import p311_rank as P
wv=sp.Rational(-1,2)+sp.sqrt(-3)/2; K=sp.QQ.algebraic_field(sp.sqrt(-3))
for tag in sys.argv[1:]:
    if tag=='pt': m,c,x,cp,xp=P.famA('0',wv)
    else:
        m,c,x,cp,xp=P.famA('1',wv); pv=sp.Rational(tag); x=[sp.sympify(e).subs(P.p,pv) for e in x]; xp=[sp.sympify(e).subs(P.p,pv) for e in xp]
    B=P.basis(m,c,x,cp,xp)
    ok=sp.expand(perm(sp.ones(5,5)+bigY(B))-120)==0
    A=fo_matrix(B); dm=sp.polys.matrices.DomainMatrix.from_Matrix(A).convert_to(K); rk=dm.rank(); N=dm.nullspace().to_Matrix()
    best=0
    for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
        H=hessian(B,yv); best=max(best,sp.polys.matrices.DomainMatrix.from_Matrix((N*H*N.T).applyfunc(sp.expand)).convert_to(K).rank())
    print('case A %-5s level %s dim T_1 = %d rank q = %d => dim L <= %d'%(tag,ok,25-rk,best,N.shape[0]-(best+1)//2),flush=True)
