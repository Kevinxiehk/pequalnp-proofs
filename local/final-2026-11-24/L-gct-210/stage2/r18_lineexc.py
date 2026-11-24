# Exceptional parameter values on a 1-parameter line for the kernel arguments [NOTES-stage2 R18-1], exact (univariate gcds):
#  (i) rank B_c(nu) < generic r (c = (1,2,3); superset via 4 random compressions), (ii) polynomial basis of the common kernel K degenerates,
#  (iii) det q0|K (polynomial basis) vanishes, (iv) setup-exceptional (dens, detX, rank-jump). Prints the union of roots (as factors).
import sys, pickle, random, itertools, sympy as sp
from sympy.polys.matrices import DomainMatrix
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(sys.argv[1],'rb'))
t=par[0]; R=sp.QQ[t]; F=sp.QQ.frac_field(t); DM=lambda M,d=F: DomainMatrix.from_Matrix(M).convert_to(d)
B=Gs[1]+2*Gs[2]+3*Gs[3]; r=DM(B).rank()
random.seed(5); g=0
for _ in range(4):
    U=sp.Matrix(r,nq,lambda i,j: random.randint(-3,3)); d=DM(U*B*U.T,R).det().as_expr(); g=sp.gcd(g,d) if g!=0 else d
K=DM(sp.Matrix.vstack(*Gs[1:])).nullspace().to_Matrix()
K=sp.Matrix.vstack(*[(K.row(i)*sp.lcm([sp.fraction(sp.together(x))[1] for x in K.row(i)])).applyfunc(sp.cancel) for i in range(K.rows)])
gm=0
for c in itertools.combinations(range(nq),K.rows):
    x=sp.expand(K.extract(list(range(K.rows)),list(c)).det())
    if x!=0: gm=sp.gcd(gm,x) if gm!=0 else x
dq=sp.factor((K*Gs[0]*K.T).det())
ex=sp.factor(sp.prod([sp.fraction(sp.together(x))[0] for x in list(dens)+[detX,rkjump]]))
print('fix',fix,'| rank drop of B_c:',sp.factor(g),'| K basis degenerate:',sp.factor(gm),'| det q0|K:',dq,'| setup-exceptional:',ex,flush=True)
allf=set()
for e in [g,gm,dq,ex]:
    for f,_ in sp.factor_list(sp.expand(e),t)[1]:
        if sp.Poly(f,t).degree()>0: allf.add(sp.factor(f))
print('  exceptional nu (roots of):',sorted(map(str,allf)),flush=True)
