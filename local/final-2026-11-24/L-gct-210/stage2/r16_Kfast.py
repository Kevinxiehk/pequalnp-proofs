# KERNEL KILL for an F2col ruling, exact over Q(params) [NOTES-stage2 R15-4]. With k spanning the common kernel of the B_z over Q(params),
# normalised k_i = 1, and rank B_c = nq - 1 over Q(params):  adj(B_c) = cof_ii(B_c) k k^T, hence the POLYNOMIAL identity
#   Phi_c := tr(G0 adj B_c) = cof_ii(B_c) * q0(k,k)            (q0(k,k) computed exactly; cof_ii = principal (nq-1)-minor).
# Pointwise lemma (any parameter point outside the setup-exceptional loci): a 4-dim L'' isotropic for G0 and B_c forces Phi_c = 0.
import sys, pickle, sympy as sp
from sympy.polys.matrices import DomainMatrix
ck=sys.argv[1]; cs=[tuple(int(x) for x in c.split(',')) for c in sys.argv[2:]] or [(1,2,3)]
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
F=sp.QQ.frac_field(*par); R=sp.QQ[tuple(par)]; DM=lambda M,d: DomainMatrix.from_Matrix(M).convert_to(d)
print('parameters',par,' nq',nq,' detX',sp.factor(detX) if detX is not None else None,' rkjump',rkjump,' dens',[sp.factor(d) for d in dens],flush=True)
G0=Gs[0]; Bst=sp.Matrix.vstack(*Gs[1:]); rs=DM(Bst,F).rank(); print('rank of B-stack over Q(params):',rs,flush=True)
assert rs==nq-1, 'common kernel not 1-dim: lemma variant needed'
K=DM(Bst,F).nullspace().to_Matrix().applyfunc(sp.cancel); k=K.row(0)
i=[j for j in range(nq) if sp.simplify(k[j]-1)==0][0]; print('k normalised at index',i,'; k =',[sp.factor(x) for x in k],flush=True)
assert all(sp.simplify(e)==0 for e in (Bst*k.T)), 'k not in the common kernel'
qkk=sp.factor(sp.cancel((k*G0*k.T)[0,0])); print('q0(k,k) =',qkk,flush=True)
for c in cs:
    B=sum((ci*G for ci,G in zip(c,Gs[1:])),sp.zeros(nq,nq)); rb=DM(B,F).rank(); print('c=%s: rank B_c over Q(params) = %d'%(c,rb),flush=True)
    if rb!=nq-1: print('  skip (rank != nq-1)'); continue
    idx=[j for j in range(nq) if j!=i]; M=B.extract(idx,idx)
    cof=sp.factor(DM(M,R).det().as_expr()); print('  cof_ii(B_c) =',cof,flush=True)
    print('  Phi_c = (%s) * (%s)'%(cof,qkk),flush=True)
