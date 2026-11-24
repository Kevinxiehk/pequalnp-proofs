# Kernel-kill analysis of a cached F2col (sub)family [NOTES-stage2 R15-4/5, R16]. nq = 8 (dim L'' = 4):
#   if the B_z have a 1-dim common kernel C k and rank B_c = 7 at a point, then k in L'' and q0(k,k) = 0 there.
# Output: ranks; k (constant?); q0(k,k); cofactors cof_ii(B_c) for sampled c; the exact common rank-drop locus (Groebner over Q) outside the
# setup-exceptional factors (dens, detX, rkjump); hence the survivor set  V(q0(k,k)) U (common rank-drop locus) U exceptional.
import sys, pickle, random, itertools, sympy as sp
from sympy.polys.matrices import DomainMatrix
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(sys.argv[1],'rb'))
CS=[(1,2,3),(1,-1,2),(2,1,-1),(3,-2,1)]
F=sp.QQ.frac_field(*par) if par else sp.QQ; R=sp.QQ[tuple(par)] if par else sp.QQ
DM=lambda M,d=F: DomainMatrix.from_Matrix(M).convert_to(d)
print('fix',fix,' parameters',par,' nq',nq,flush=True)
exc_raw=[sp.fraction(sp.together(x))[0] for x in list(dens)+[detX,rkjump]]
EXC=[]
for x in exc_raw:
    if par:
        for f,e in sp.factor_list(sp.expand(x),*par)[1]:
            if sp.Poly(f,*par).total_degree()>0 and all(sp.simplify(f/g).free_symbols for g in EXC) : EXC.append(f)
print('setup-exceptional factors:',EXC,flush=True)
print('rank q0 =',DM(Gs[0]).rank(),'; ranks B_z =',[DM(G).rank() for G in Gs[1:]],flush=True)
Bst=sp.Matrix.vstack(*Gs[1:]); rs=DM(Bst).rank(); print('rank B-stack =',rs,flush=True)
Bc=lambda c: sum((ci*G for ci,G in zip(c,Gs[1:])),sp.zeros(nq,nq))
rc=DM(Bc(CS[0])).rank(); print('rank B_(1,2,3) =',rc,flush=True)
if (nq!=8 or rs!=7 or rc!=7) and rs==nq-1:
    # JUMP-TYPE LEMMA (NOTES-stage2 R15-6): if some B_z has rank r_z with 4 - floor(r_z/2) >= 1, L'' meets W_z = ker B_z; if on W_z the other B_w have
    # rank <= 1 (B_w|W = l_w^2) and the l_w cut W_z down to the common kernel C k, then k in L'' and q0(k,k) = 0.
    k=DM(Bst).nullspace().to_Matrix().row(0).applyfunc(sp.cancel); qkk=sp.factor(sp.cancel((k*Gs[0]*k.T)[0,0]))
    print('common kernel k =',[sp.factor(x) for x in k],'; q0(k,k) =',qkk,flush=True)
    ok=False
    for z in range(1,len(Gs)):
        rz=DM(Gs[z]).rank()
        if 4-rz//2<1: print('z=%d: rank %d too large for the meeting argument'%(z,rz),flush=True); continue
        W=DM(Gs[z]).nullspace().to_Matrix().applyfunc(sp.cancel); oth=[w for w in range(1,len(Gs)) if w!=z]
        Rw=[(W*Gs[w]*W.T).applyfunc(sp.cancel) for w in oth]; rks=[DM(M).rank() for M in Rw]
        st=DM(sp.Matrix.vstack(*Rw)).rank() if all(x<=1 for x in rks) else None
        print('z=%d: rank B_z %d, dim W_z %d, ranks of other B_w on W_z %s, rank of their stack %s'%(z,rz,W.rows,rks,st),flush=True)
        if all(x<=1 for x in rks) and st is not None and W.rows-st==1: ok=True
    if ok and par:
        qf=[f for f,e in sp.factor_list(sp.expand(sp.fraction(sp.together(qkk))[0]),*par)[1] if sp.Poly(f,*par).total_degree()>0]
        print('JUMP-TYPE KILL applies generically: SURVIVORS: V(q0(k,k)) factors (non-exceptional):',[f for f in qf if not any(sp.simplify(f/g).is_number for g in EXC)],' U Deg (r16_Kjump_deg.py) U exceptional',flush=True)
        sys.exit(0)
    if ok and not par:
        print('FIXED MEMBER (jump-type): q0(k,k) %s 0 -> %s'%('!=' if qkk!=0 else '==','KILLED by the jump-type lemma' if qkk!=0 else 'not killed'),flush=True); sys.exit(0)
if nq!=8 or rs!=7 or rc!=7:
    print('NOT the standard case (need nq = 8, B-stack rank 7, B_c rank 7): manual analysis',flush=True)
    if rs<nq:
        K=DM(Bst).nullspace().to_Matrix().applyfunc(sp.cancel); print('common kernel basis:',K.tolist(),flush=True)
        print('q0 on the common kernel:',(K*Gs[0]*K.T).applyfunc(sp.factor).tolist(),flush=True)
    sys.exit(0)
k=DM(Bst).nullspace().to_Matrix().row(0).applyfunc(sp.cancel)
consts=[j for j in range(nq) if k[j]!=0 and sp.sympify(k[j]).is_number]
i=consts[0]; k=k/k[i]; print('k =',[sp.factor(x) for x in k],' (constant: %s)'%all(sp.sympify(x).is_number for x in k),flush=True)
assert all(sp.expand(sp.cancel(e))==0 for e in Bst*k.T)
qkk=sp.factor(sp.cancel((k*Gs[0]*k.T)[0,0])); print('q0(k,k) =',qkk,flush=True)
if not par:
    print('FIXED MEMBER: q0(k,k) %s 0 -> %s'%('!=' if qkk!=0 else '==', 'KILLED by the kernel lemma' if qkk!=0 else 'not killed: run r16_F2col_K'),flush=True); sys.exit(0)
fams=[]; idx=[j for j in range(nq) if j!=i]
for c in CS:
    B=Bc(c)
    if DM(B).rank()!=7: print('c=%s: rank != 7, skipped'%(c,),flush=True); continue
    cof=sp.factor(DM(B.extract(idx,idx),R).det().as_expr()); print('c=%s: cof =',cof if len(str(cof))<600 else str(cof)[:600]+'...',flush=True)
    keep=[f for f,e in sp.factor_list(sp.expand(cof),*par)[1] if sp.Poly(f,*par).total_degree()>0 and not any(sp.simplify(f/g).is_number for g in EXC)]
    fams.append(keep); print('   non-exceptional factors:',keep,flush=True)
comps=set()
for ch in itertools.product(*fams):
    G=sp.groebner(list(set(ch)),*par,order='lex')
    if list(G)!=[1]: comps.add(tuple(G))
print('COMMON RANK-DROP LOCUS (outside exceptional), Groebner components:',flush=True)
for G in sorted(comps,key=str): print('   ',list(G),flush=True)
qf=[f for f,e in sp.factor_list(sp.expand(sp.fraction(sp.together(qkk))[0]),*par)[1] if sp.Poly(f,*par).total_degree()>0]
print('SURVIVORS: V(q0(k,k)) factors (non-exceptional):',[f for f in qf if not any(sp.simplify(f/g).is_number for g in EXC)],' U rank-drop components above U exceptional',flush=True)
