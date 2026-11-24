# Degeneracy locus Deg of the JUMP-TYPE lemma for ANY cached family [NOTES-stage2 R17; generalises r16_Kjump_deg.py].
# Lemma via index z (pointwise at pi): (a) rank B_z(pi) = r_z (generic rank) with 4 - floor(r_z/2) >= 1, (b) the polynomial basis N_z of ker B_z keeps
# full rank, (c) the restrictions R_w = N_z B_w N_z^T (rank <= 1 identically) of the other two forms have a rank-2 stack  =>  L'' contains the common
# kernel vector k. z is USABLE only if (a)-(c) hold over Q(params). Deg = intersection over usable z of the failure sets (supersets via
# certificates: random r_z x r_z compressions; all maximal minors of N_z; all 2-minors of the stack); exact Groebner over Q.
# Also prints the survivors V(q0(k,k)).   usage: r17_Kjump_deg.py CACHE
import sys, pickle, random, itertools, sympy as sp
from sympy.polys.matrices import DomainMatrix
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(sys.argv[1],'rb'))
F=sp.QQ.frac_field(*par) if par else sp.QQ; R=sp.QQ[tuple(par)] if par else sp.QQ
DM=lambda M,d=F: DomainMatrix.from_Matrix(M).convert_to(d)
print('fix',fix,'params',par,'nq',nq,flush=True)
k=DM(sp.Matrix.vstack(*Gs[1:])).nullspace().to_Matrix(); assert k.rows==1, 'common kernel not 1-dim'
k=k.row(0).applyfunc(sp.cancel); print('k =',list(k),'; q0(k,k) =',sp.factor(sp.cancel((k*Gs[0]*k.T)[0,0])),flush=True)
random.seed(13); fails={}
for z in (1,2,3):
    rz=DM(Gs[z]).rank()
    if 4-rz//2<1: print('z=%d: rank %d, meeting argument unavailable -> not usable'%(z,rz),flush=True); continue
    N=DM(Gs[z]).nullspace().to_Matrix()
    N=sp.Matrix.vstack(*[(N.row(r)*sp.lcm([sp.fraction(sp.together(x))[1] for x in N.row(r)])).applyfunc(sp.cancel) for r in range(N.rows)])
    oth=[w for w in (1,2,3) if w!=z]; Rw=[(N*Gs[w]*N.T).applyfunc(sp.expand) for w in oth]
    if not all(DM(M).rank()<=1 for M in Rw): print('z=%d: other forms not rank <= 1 on ker B_z -> not usable'%z,flush=True); continue
    St=sp.Matrix.vstack(*Rw)
    if N.rows-DM(St).rank()!=1: print('z=%d: l_w do not cut ker B_z down to C k -> not usable'%z,flush=True); continue
    U=[sp.Matrix(rz,nq,lambda i,j: random.randint(-3,3)) for _ in range(3)]
    Ja=[sp.expand(DM(u*Gs[z]*u.T,R).det().as_expr()) for u in U]
    Jb=[sp.expand(N.extract(list(range(N.rows)),list(c)).det()) for c in itertools.combinations(range(nq),N.rows)]
    Jc=[sp.expand(St.extract(list(r),list(c)).det()) for r in itertools.combinations(range(St.rows),2) for c in itertools.combinations(range(N.rows),2)]
    fails[z]=[[p for p in J if p!=0] for J in (Ja,Jb,Jc)]
    if par:
        for nm,J in zip('abc',fails[z]): print('z=%d (rank %d) (%s): V = %s'%(z,rz,nm,[sp.factor(g) for g in sp.groebner(J,*par,order='lex')] if J else 'everything'),flush=True)
    else: print('z=%d usable; certificates at the point:'%z,[any(p!=0 for p in J) for J in fails[z]],flush=True)
if not fails: print('NO usable z: lemma unavailable',flush=True); sys.exit(0)
if not par:
    ok=any(all(any(p!=0 for p in J) for J in fails[z]) for z in fails)
    print('FIXED MEMBER: lemma applies at the point:',ok,flush=True); sys.exit(0)
out=set()
for ch in itertools.product(range(3),repeat=len(fails)):
    J=sum((fails[z][c] for z,c in zip(sorted(fails),ch)),[])
    G=sp.groebner(J,*par,order='lex')
    if list(G)!=[1]: out.add(tuple(sp.factor(g) for g in G))
print('Deg (intersection over usable z of the unions):',flush=True)
for G in sorted(out,key=str): print('  ',list(G),flush=True)
if not out: print('   EMPTY',flush=True)
