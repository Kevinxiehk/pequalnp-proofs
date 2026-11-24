# ADJUGATE KILL for an F2col ruling (cached v4 setup) [NOTES-stage2 R15-4]. Forms on the complement C (dim nq = 8): G0 = q0, B_c = sum c_z B_z.
# Lemma: if a 4-dim L'' in C is isotropic for G0 and B_c, then Phi_c := tr(G0 adj B_c) = 0. (rank B_c = 7 => adj B_c = mu k k^T, mu != 0,
# k in L'' by the isotropic-dimension bound in C/Ck, so q0(k,k) = 0; rank B_c <= 6 => adj B_c = 0.)  Phi_c = sum_i det(B_c with column i := G0 column i).
import sys, pickle, sympy as sp
from sympy.polys.matrices import DomainMatrix
ck=sys.argv[1]; cs=[tuple(int(x) for x in c.split(',')) for c in sys.argv[2:]] or [(1,2,3)]
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
R=sp.QQ[tuple(par)]
print('parameters',par,' nq',nq,flush=True)
print('setup exceptional data: detX =',sp.factor(detX) if detX is not None else None,' rkjump =',rkjump,' dens =',[sp.factor(d) for d in dens],flush=True)
G0=Gs[0]; facs=[]
for c in cs:
    B=sum((ci*G for ci,G in zip(c,Gs[1:])),sp.zeros(nq,nq))
    Phi=0
    for i in range(nq):
        M=B.copy(); M[:,i]=G0[:,i]
        Phi+=DomainMatrix.from_Matrix(M).convert_to(R).det().as_expr()
        print('  c=%s column %d done'%(c,i),flush=True)
    f=sp.factor_list(sp.expand(Phi)); facs.append(f)
    print('Phi_%s = %s * %s'%(c,f[0],' * '.join('(%s)^%d'%(g,e) for g,e in f[1])),flush=True)
common=None
for f in facs:
    S=set(sp.expand(g) for g,e in f[1]); common=S if common is None else common&S
print('irreducible factors common to all Phi_c:',[sp.factor(g) for g in common],flush=True)
