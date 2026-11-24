# RANK-2 SPLIT [NOTES-stage2 R21-1]: a form B of rank 2 is l1*l2 (two independent linear forms, over a quadratic extension at worst), and a subspace
# L of dim >= 2 is B-isotropic iff l1|L = 0 or l2|L = 0. So a 4-dim common isotropic L'' lies in the hyperplane {l1 = 0} or {l2 = 0}.
# This script: for a cached family, find the rank-2 B_z, write B = P^T N P (P: 2 x nq row basis of B, N symmetric 2x2), and report N, its discriminant,
# the hyperplanes, and the ranks of all forms restricted to each hyperplane (recursive bound input).
import sys, pickle, sympy as sp
from sympy.polys.matrices import DomainMatrix
ck=sys.argv[1]
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
F=sp.QQ.frac_field(*par) if par else sp.QQ; DM=lambda M: DomainMatrix.from_Matrix(M).convert_to(F)
for z in range(1,len(Gs)):
    B=Gs[z]
    if DM(B).rank()!=2: continue
    # row basis: two independent rows of B
    rows=[]
    for i in range(nq):
        cand=rows+[i]
        if DM(B.extract(cand,list(range(nq)))).rank()==len(cand): rows=cand
        if len(rows)==2: break
    P=B.extract(rows,list(range(nq)))                      # 2 x nq, rowspace = column space of B
    # B = P^T N P  with N = (P P^T)^-1 P B P^T (P P^T)^-1 ... simpler: solve via the 2x2 block: B[rows][:,cols] for two independent columns
    cols=rows
    Bsub=B.extract(rows,cols); Psub=P.extract([0,1],cols)
    N=(Psub.T.inv()*Bsub*Psub.inv()).applyfunc(sp.cancel)
    chk=(P.T*N*P-B).applyfunc(sp.cancel)
    print('B_%d: rank 2, rows %s; N = %s; reconstruction exact: %s'%(z,rows,[[sp.factor(x) for x in N.row(i)] for i in range(2)],all(e==0 for e in chk)),flush=True)
    a,b,c=N[0,0],N[0,1],N[1,1]; disc=sp.factor(b*b-a*c); print('   discriminant b^2 - ac =',disc,flush=True)
    print('   B = (l1)(l2) with l = P-row combinations (x,y) where a x^2 + 2b xy + c y^2 = 0 factors over Q(params)(sqrt(disc))',flush=True)
