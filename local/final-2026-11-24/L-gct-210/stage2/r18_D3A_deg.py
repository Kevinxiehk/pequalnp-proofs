# Degeneracy locus of the BIG-KERNEL kill for D003-PROP Case A [NOTES-stage2 R18-2]. Lemma at a point pi (a2 != 1, a2+a3+1 != 0, generic T_1):
#   some B_c has rank 5 with ker B_c = K(pi) (polynomial basis of K of full rank 3) and det q0|K(pi) != 0  =>  no 4-dim common isotropic L''
#   (L'' meets K in dim >= 2, but a nondegenerate ternary form has no isotropic plane).
# Failure set (superset): [V(5x5 compressions of B_c1) cap V(... of B_c2)] u V(3-minors of the K basis) u V(det q0|K). Exact Groebner over Q.
import pickle, random, itertools, sympy as sp
from sympy.polys.matrices import DomainMatrix
_,_,_,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open('/home/kevxhk/work/L-gct-210/stage2/r18/cache_D3A.pkl','rb'))
F=sp.QQ.frac_field(*par); R=sp.QQ[tuple(par)]; DM=lambda M,d=F: DomainMatrix.from_Matrix(M).convert_to(d)
q0=Gs[0]; Bs=Gs[1:]
fails=[]
for seed in (2,7):
    random.seed(seed); c=[random.randint(1,9) for _ in Bs]; B=sum((ci*M for ci,M in zip(c,Bs)),sp.zeros(nq,nq))
    J=[]
    for _ in range(4):
        U=sp.Matrix(5,nq,lambda i,j: random.randint(-3,3)); J.append(sp.expand(DM(U*B*U.T,R).det().as_expr()))
    G=sp.groebner([x for x in J if x!=0],*par,order='lex'); fails.append(list(G)); print('c =',c,': rank < 5 only on V(',[sp.factor(g) for g in G],')',flush=True)
Grank=sp.groebner(fails[0]+fails[1],*par,order='lex'); print('rank < 5 for both c only on V(',[sp.factor(g) for g in Grank],')',flush=True)
K=DM(sp.Matrix.vstack(*Bs)).nullspace().to_Matrix()
K=sp.Matrix.vstack(*[(K.row(i)*sp.lcm([sp.fraction(sp.together(x))[1] for x in K.row(i)])).applyfunc(sp.cancel) for i in range(K.rows)])
assert all(sp.expand(e)==0 for M in Bs for e in M*K.T)
mins=[sp.expand(K.extract([0,1,2],list(cc)).det()) for cc in itertools.combinations(range(nq),3)]
Gb=sp.groebner([x for x in mins if x!=0],*par,order='lex'); print('K basis degenerates only on V(',[sp.factor(g) for g in Gb],')',flush=True)
dq=sp.factor((K*q0*K.T).det()); print('det q0|K =',dq,flush=True)
print('setup-exceptional: detX',sp.factor(detX),'| den',[sp.factor(d) for d in dens],'| rank-jump',rkjump,flush=True)
