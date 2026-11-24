# Recursive kernel bound on a 1-PARAMETER family with its exact exceptional set, then pointwise checks [NOTES-stage2 R21-2].
# Generic step (over Q(t)): find a contradicting chain V > ker G1 > ker G2|W1 > ... ; record at each step the rank r_i and (univariate) the polynomial
# whose roots contain every t where that rank drops (gcd of random r_i x r_i compressions) or where the polynomial kernel basis degenerates, and for the
# final space the rank rho of a fixed combination. The kill holds for all t off the roots (and off EXC). Each irreducible factor of the exceptional
# polynomial is then checked at one root by the full recursion over the number field (r21_algpoint.py logic; conjugates behave identically).
# usage: r21_chain.py CACHE ["z:r" rank-2 branch hyperplane]
import sys, pickle, random, itertools, subprocess, sympy as sp
from sympy.polys.matrices import DomainMatrix
ck=sys.argv[1]; hyp=sys.argv[2] if len(sys.argv)>2 else ''
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
assert len(par)==1; t=par[0]; F=sp.QQ.frac_field(t); R=sp.QQ[t]
DM=lambda M,d=F: DomainMatrix.from_Matrix(M).convert_to(d)
pb=lambda N: sp.Matrix.vstack(*[(N.row(i)*sp.lcm([sp.fraction(sp.together(x))[1] for x in N.row(i)])).applyfunc(sp.cancel) for i in range(N.rows)])
names=['q0']+['B%d'%z for z in range(1,len(Gs))]
random.seed(3); CW=[random.randint(1,9) for _ in Gs]
def gcd_compr(M,r):
    g=0
    for _ in range(3):
        U=sp.Matrix(r,M.rows,lambda i,j: random.randint(-3,3)); d=DM(U*M*U.T,R).det().as_expr(); g=sp.gcd(g,d) if g!=0 else d
    return sp.expand(g)
def gcd_maxminors(Mb):
    g=0
    for cc in itertools.combinations(range(Mb.cols),Mb.rows):
        x=sp.expand(Mb.extract(list(range(Mb.rows)),list(cc)).det())
        if x!=0: g=sp.gcd(g,x) if g!=0 else x
    return sp.expand(g)
excp=[]
def node(basis,m,path):
    n=basis.rows; forms=[(basis*G*basis.T).applyfunc(sp.expand) for G in Gs]
    comb=sum((c*f for c,f in zip(CW,forms)),sp.zeros(n,n)); rho=DM(comb).rank() if n else 0; maxiso=(n-rho)+rho//2
    if m>maxiso or m>n:
        if rho>0: excp.append(('final rho=%d on %s'%(rho,' > '.join(path)),gcd_compr(comb,rho)))
        excp.append(('basis at %s'%' > '.join(path),gcd_maxminors(basis)))
        print('  CHAIN: %s: dim %d, need %d, max isotropic %d'%(' > '.join(path),n,m,maxiso),flush=True); return True
    if m<=0 or len(path)>5: return False
    for nm,f in zip(names,forms):
        r=DM(f).rank()
        if r==0 or r==n or m-r//2<=0: continue
        W=(pb(DM(f).nullspace().to_Matrix())*basis).applyfunc(sp.expand)
        if node(W,m-r//2,path+['ker %s (rank %d)'%(nm,r)]):
            excp.append(('rank %s = %d at %s'%(nm,r,' > '.join(path)),gcd_compr(f,r))); excp.append(('basis at %s'%' > '.join(path),gcd_maxminors(basis))); return True
    return False
start=sp.eye(nq); tag='V'
if hyp:
    zz,rr=[int(x) for x in hyp.split(':')]; start=pb(DM(Gs[zz].row(rr)).nullspace().to_Matrix()); tag='H(B%d row %d)'%(zz,rr)
print('fix',fix,'| setup detX',sp.factor(detX),'dens',[sp.factor(d) for d in dens],'rank-jump',rkjump,flush=True)
ok=node(start,4,[tag])
if not ok: print('RESULT: no contradicting chain (generic)',flush=True); sys.exit(0)
allf=set()
for lab,p in excp+[('setup',sp.prod([sp.fraction(sp.together(x))[0] for x in list(dens)+[detX,rkjump]]))]:
    for f,_ in sp.factor_list(sp.expand(p),t)[1]:
        if sp.Poly(f,t).degree()>0: allf.add(sp.factor(f))
print('generic KILL; exceptional t = roots of',sorted(map(str,allf)),flush=True)
for f in sorted(allf,key=str):
    o=subprocess.run(['timeout','900','python3','-I','/home/kevxhk/work/L-gct-210/stage2/r21_algpoint.py',ck,str(f),hyp,'4','5'],capture_output=True,text=True).stdout
    v=[l for l in o.splitlines() if l.startswith('RESULT')]
    print('   at root of %s: %s'%(f,v[0] if v else 'ERROR '+o[-200:]),flush=True)
