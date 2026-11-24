# RECURSIVE general kernel bound [NOTES-stage2 R20-3]. A totally isotropic L (dim m) for forms {G} on V meets ker(G|V) in dim >= m - floor(rank(G|V)/2).
# Recurse into W = ker(G|V) with all forms restricted and the new bound; a node is CONTRADICTORY if the bound exceeds the maximal isotropic dimension of
# the common forms on W, (dim W - rho) + floor(rho/2) with rho = rank of a generic combination, or exceeds dim W. Over Q(params) (generic statement).
# usage: r20_kbound_rec.py CACHE [m=4] [depth=3]
import sys, pickle, random, sympy as sp
from sympy.polys.matrices import DomainMatrix
ck=sys.argv[1]; M0=int(sys.argv[2]) if len(sys.argv)>2 else 4; DEP=int(sys.argv[3]) if len(sys.argv)>3 else 3
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
import os
BASE=sp.QQ.algebraic_field(sp.I) if os.environ.get('QI') else sp.QQ
F=BASE.frac_field(*par) if par else BASE; DM=lambda M: DomainMatrix.from_Matrix(M).convert_to(F)
names=['q0']+['B%d'%z for z in range(1,len(Gs))]
random.seed(1)
def rk(M): return DM(M).rank() if M.rows else 0
def node(basis,m,path,d):
    n=basis.rows
    forms=[(basis*G*basis.T).applyfunc(sp.cancel) for G in Gs]
    comb=sum((random.randint(1,9)*f for f in forms),sp.zeros(n,n)); rho=rk(comb); maxiso=(n-rho)+rho//2
    tag=' > '.join(path) if path else 'V'
    if m>maxiso or m>n: print('  %s: dim %d, need %d, max isotropic %d -> CONTRADICTION'%(tag,n,m,maxiso),flush=True); return True
    if m<=0: print('  %s: dim %d, need %d -> no constraint'%(tag,n,m),flush=True); return False
    if d==DEP: print('  %s: dim %d, need %d, max isotropic %d -> depth limit'%(tag,n,m,maxiso),flush=True); return False
    for nm,f in zip(names,forms):
        r=rk(f)
        if r==0 or r==n: continue
        m2=m-r//2
        if m2<=0: continue
        W=DM(f).nullspace().to_Matrix().applyfunc(sp.cancel)
        Wb=(W*basis).applyfunc(sp.cancel)
        if node(Wb,m2,path+['ker %s (rank %d on dim %d)'%(nm,r,n)],d+1): return True
    print('  %s: dim %d, need %d: no contradiction found'%(tag,n,m),flush=True); return False
print('fix',fix,'params',par,'nq',nq,flush=True)
res=node(sp.eye(nq),M0,[],0)
print('RESULT recursive kernel bound:', 'KILLED (generic member)' if res else 'not decided',flush=True)
