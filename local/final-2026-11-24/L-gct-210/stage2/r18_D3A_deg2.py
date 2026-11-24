# Fast degeneracy locus of the BIG-KERNEL kill for D003-PROP Case A [NOTES-stage2 R18-2]. With K = common kernel (rref, pivots P, |P| = 3) and Q the
# complementary 5 coordinates, the Q-coordinate subspace is a complement of K wherever the rref of K is defined, so rank B_c = 5 <=> det B_c[Q,Q] != 0.
# Failure set: V(det B_c1[Q,Q]) cap V(det B_c2[Q,Q]) u {rref(K) undefined} u V(det q0|K) u setup-exceptional. Exact over Q (2 parameters).
import pickle, random, sympy as sp
from sympy.polys.matrices import DomainMatrix
_,_,_,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open('/home/kevxhk/work/L-gct-210/stage2/r18/cache_D3A.pkl','rb'))
F=sp.QQ.frac_field(*par); R=sp.QQ[tuple(par)]; DM=lambda M,d=F: DomainMatrix.from_Matrix(M).convert_to(d)
q0=Gs[0]; Bs=Gs[1:]
K=DM(sp.Matrix.vstack(*Bs)).nullspace().to_Matrix()
Rr,piv=DomainMatrix.from_Matrix(K).convert_to(F).rref(); Kr=Rr.to_Matrix().applyfunc(sp.cancel)
den=sp.factor(sp.lcm([sp.fraction(sp.together(x))[1] for x in Kr])); Q=[j for j in range(nq) if j not in piv]
print('pivots of K',piv,'| complement coords',Q,'| rref(K) denominators',den,flush=True)
dets=[]
for seed in (2,7,11):
    random.seed(seed); c=[random.randint(1,9) for _ in Bs]; B=sum((ci*M for ci,M in zip(c,Bs)),sp.zeros(nq,nq))
    d=sp.factor(DM(B.extract(Q,Q),R).det().as_expr()); dets.append(d); print('c =',c,': det B_c[Q,Q] =',d,flush=True)
g=dets[0]
for d in dets[1:]: g=sp.gcd(g,d)
print('gcd over the 3 combinations (common codim-1 rank-drop part):',sp.factor(g),flush=True)
Gb=sp.groebner([sp.expand(sp.cancel(d/g)) for d in dets],*par,order='lex'); print('residual common zeros of the reduced dets: V(',[sp.factor(x) for x in Gb],')',flush=True)
Kp=(Kr*den).applyfunc(lambda x: sp.expand(sp.cancel(x)))
dq=sp.factor((Kp*q0*Kp.T).det()); print('det q0|K (rref basis scaled by den) =',dq,flush=True)
print('setup-exceptional: detX',sp.factor(detX),'| den',[sp.factor(x) for x in dens],'| rank-jump',rkjump,flush=True)
