# verify2 r25: my own check of stage2 R17-3 (special Z n = (1,0,0,0), big-kernel lemma) from the cache r16/cache_8b37b704738a.pkl.
import pickle, sympy as sp, random
from sympy.polys.matrices import DomainMatrix
d=pickle.load(open('/home/kevxhk/work/L-gct-210/stage2/r16/cache_8b37b704738a.pkl','rb'))
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=d
print('par',par,'nq',nq,'dens',dens,'detX',detX,'rkjump',rkjump)
F=sp.QQ.frac_field(*par)
K=DomainMatrix.from_Matrix(sp.Matrix.vstack(*Gs[1:])).convert_to(F).nullspace().to_Matrix()
K=sp.Matrix.vstack(*[(K.row(i)*sp.lcm([sp.fraction(sp.together(x))[1] for x in K.row(i)])).applyfunc(sp.cancel) for i in range(K.rows)])
print('common kernel dim',K.rows,' basis polynomial:',all(sp.fraction(sp.together(x))[1].is_number for x in K))
Q=(K*Gs[0]*K.T).applyfunc(sp.cancel); dq=sp.factor(Q.det()); print('det q0|K =',dq)
# rank of the 3 x 3 minors of K (basis degeneracy): gcd of all 3x3 minors
from itertools import combinations
g=0
for c in combinations(range(nq),3): g=sp.gcd(g,K.extract([0,1,2],list(c)).det())
print('gcd of 3x3 minors of K (basis degeneracy):',sp.factor(g))
for c in [(1,2,3),(2,-1,5),(3,1,-2)]:
    Bc=sum((ci*Gs[i+1] for i,ci in enumerate(c)),sp.zeros(nq)); r=DomainMatrix.from_Matrix(Bc).convert_to(F).rank()
    print('c',c,'generic rank B_c',r)
for nv in [0,sp.Rational(5,7)]:
    pass
# rank-drop locus of B_c (rank 5 generic): gcd over random c of the gcd of all 5x5 minors
from itertools import combinations
random.seed(2)
G=0
for trial in range(3):
    c=[random.randint(1,30) for _ in range(3)]
    Bc=sum((ci*Gs[i+1] for i,ci in enumerate(c)),sp.zeros(nq)).applyfunc(sp.cancel)
    g=0
    for rs in combinations(range(nq),5):
        for cs in combinations(range(nq),5):
            m=sp.cancel(Bc.extract(list(rs),list(cs)).det())
            if m!=0: g=sp.gcd(g,sp.numer(sp.together(m)))
            if g!=0 and sp.degree(g,nu)==0: break
        if g!=0 and sp.degree(g,nu)==0: break
    G=sp.gcd(G,g); print('c',c,'gcd of 5x5 minors (numerators):',sp.factor(g))
print('rank B_c < 5 for all sampled c only at roots of',sp.factor(G))
