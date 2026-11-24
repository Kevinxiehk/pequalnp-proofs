# Degeneracy locus Deg of the jump-locus kernel lemma (r16_Kjump.py) [NOTES-stage2 R15-6]. At a point pi the lemma (k0 in L'') holds via index z if
#  (a) rank B_z(pi) = 7, (b) the polynomial basis N_z of ker B_z (denominators cleared) has rank 3 at pi, (c) [R_w ; R_w'] (R_w = N_z B_w N_z^T, rank <= 1
#  identically) has rank 2 at pi.  Superset certificates: (a) fails => 3 random 7x7 compressions vanish; (b) fails => all 3-minors of N_z vanish;
#  (c) fails => all 2-minors of the 6x3 stack vanish.  Deg = intersection over z of the union of the three failure sets; exact Groebner over Q.
import sys, pickle, random, itertools, sympy as sp
from sympy.polys.matrices import DomainMatrix
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(sys.argv[1],'rb'))
F=sp.QQ.frac_field(*par); R=sp.QQ[tuple(par)]; DM=lambda M,d=F: DomainMatrix.from_Matrix(M).convert_to(d)
random.seed(13); fails={}
for z in (1,2,3):
    U=[sp.Matrix(7,nq,lambda i,j: random.randint(-3,3)) for _ in range(3)]
    Ja=[sp.expand(DM(u*Gs[z]*u.T,R).det().as_expr()) for u in U]
    N=DM(Gs[z]).nullspace().to_Matrix()
    N=sp.Matrix.vstack(*[ (N.row(r)*sp.lcm([sp.fraction(sp.together(x))[1] for x in N.row(r)])).applyfunc(sp.cancel) for r in range(N.rows)])
    assert all(sp.expand(e)==0 for e in Gs[z]*N.T)
    Jb=[sp.expand(N.extract([0,1,2],list(c)).det()) for c in itertools.combinations(range(nq),3)]
    others=[w for w in (1,2,3) if w!=z]; St=sp.Matrix.vstack(*[(N*Gs[w]*N.T).applyfunc(sp.expand) for w in others])
    for w in others:
        Rw=(N*Gs[w]*N.T).applyfunc(sp.expand); assert all(sp.expand(Rw.extract(list(r),list(c)).det())==0 for r in itertools.combinations(range(3),2) for c in itertools.combinations(range(3),2)), 'R_w not rank <= 1'
    Jc=[sp.expand(St.extract(list(r),list(c)).det()) for r in itertools.combinations(range(6),2) for c in itertools.combinations(range(3),2)]
    fails[z]=[[p for p in J if p!=0] for J in (Ja,Jb,Jc)]
    for nm,J in zip('abc',fails[z]): print('z=%d (%s): %d nonzero certificate polynomials; V = %s'%(z,nm,len(J),list(sp.groebner(J,*par,order='lex')) if J else 'everything'),flush=True)
print('Deg (intersection over z of the unions):',flush=True)
out=set()
for ch in itertools.product(range(3),repeat=3):
    J=sum((fails[z][ch[z-1]] for z in (1,2,3)),[])
    G=sp.groebner(J,*par,order='lex')
    if list(G)!=[1]: out.add(tuple(G))
for G in sorted(out,key=str): print('  ',list(G),flush=True)
