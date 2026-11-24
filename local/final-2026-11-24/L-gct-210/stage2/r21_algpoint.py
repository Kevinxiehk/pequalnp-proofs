# Recursive kernel bound at an ALGEBRAIC parameter value (one root of an irreducible polynomial; Galois conjugates behave identically)
# [NOTES-stage2 R21-1]. Exact linear algebra over the number field. Optional restriction to the hyperplane of row r of B_z (rank-2 split branch).
# usage: r21_algpoint.py CACHE "poly in the parameter" [z:r] [m=4] [depth=4]
import sys, pickle, random, sympy as sp
from sympy.polys.matrices import DomainMatrix
ck=sys.argv[1]; pol=sys.argv[2]; hyp=sys.argv[3] if len(sys.argv)>3 and sys.argv[3] else ''; M0=int(sys.argv[4]) if len(sys.argv)>4 else 4; DEP=int(sys.argv[5]) if len(sys.argv)>5 else 4
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
t=par[0]; P=sp.Poly(sp.sympify(pol,locals={str(t):t}),t); root=sp.CRootOf(P.as_expr(),0) if P.degree()>1 else sp.solve(P.as_expr(),t)[0]
if P.degree()==2:
    root=sp.solve(P.as_expr(),t)[0]
K=sp.QQ.algebraic_field(root) if not root.is_rational else sp.QQ
print('parameter',t,'= root of',P.as_expr(),'->',root,'| field',K,flush=True)
Gr=[G.subs(t,root).applyfunc(lambda e: sp.nsimplify(sp.expand(e)) if False else sp.expand(e)) for G in Gs]
DM=lambda M: DomainMatrix.from_Matrix(M).convert_to(K)
names=['q0']+['B%d'%z for z in range(1,len(Gs))]
random.seed(1)
def rk(M): return DM(M).rank() if M.rows else 0
def nullsp(M): return DM(M).nullspace().to_Matrix()
def node(basis,m,path,d):
    n=basis.rows; forms=[(basis*G*basis.T).applyfunc(sp.expand) for G in Gr]
    comb=sum((random.randint(1,9)*f for f in forms),sp.zeros(n,n)); rho=rk(comb); maxiso=(n-rho)+rho//2
    tag=' > '.join(path)
    if m>maxiso or m>n: print('  %s: dim %d, need %d, max isotropic %d -> CONTRADICTION'%(tag,n,m,maxiso),flush=True); return True
    if m<=0 or d==DEP: print('  %s: dim %d, need %d -> stop'%(tag,n,m),flush=True); return False
    for nm,f in zip(names,forms):
        r=rk(f)
        if r==0 or r==n or m-r//2<=0: continue
        W=(nullsp(f)*basis).applyfunc(sp.expand)
        if node(W,m-r//2,path+['ker %s (rank %d on dim %d)'%(nm,r,n)],d+1): return True
    return False
start=sp.eye(nq); tag0='V'
if hyp:
    zz,rr=[int(x) for x in hyp.split(':')]; ell=Gr[zz].row(rr)
    if all(sp.simplify(x)==0 for x in ell): print('row',rr,'of B%d vanishes at this point'%zz,flush=True)
    start=nullsp(ell); tag0='H(B%d row %d)'%(zz,rr)
print('B1 rank at the point:',rk(Gr[1]),flush=True)
res=node(start,M0,[tag0],0)
print('RESULT at the algebraic point:', 'KILLED in this branch' if res else 'not decided',flush=True)
