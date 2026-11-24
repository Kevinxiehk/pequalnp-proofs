# Degeneracy data for the J_A^R1 kill [NOTES-stage2 R21-1]: branch H_j = ker(row r_j of B_1) (rank-2 split), chain
#   W = ker(B_2|H) (dim 2 when rank B_2|H = 7), w' = ker(B_3|W) (dim 1 when rank B_3|W = 1), contradiction iff q0(w', w') != 0.
# Prints, per branch, the polynomials whose vanishing can break the chain (gcd of 7-minors of B_2|H over sampled minors, entries of B_3|W, q0(w',w'),
# basis-degeneracy factors), so that the generic kill holds off their common zero set.
import sys, pickle, itertools, random, sympy as sp
from sympy.polys.matrices import DomainMatrix
ck=sys.argv[1]; ROWS=[int(x) for x in (sys.argv[2] if len(sys.argv)>2 else '2,5').split(',')]
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
F=sp.QQ.frac_field(*par); R=sp.QQ[tuple(par)]; DM=lambda M,d=F: DomainMatrix.from_Matrix(M).convert_to(d)
def polybasis(N):
    return sp.Matrix.vstack(*[(N.row(i)*sp.lcm([sp.fraction(sp.together(x))[1] for x in N.row(i)])).applyfunc(sp.cancel) for i in range(N.rows)])
print('fix',fix,'| setup: detX',sp.factor(detX),'dens',[sp.factor(d) for d in dens],'rank-jump',rkjump,flush=True)
B1,B2,B3,q0=Gs[1],Gs[2],Gs[3],Gs[0]
for r in ROWS:
    ell=B1.row(r); H=polybasis(DM(ell).nullspace().to_Matrix())
    B2H=(H*B2*H.T).applyfunc(sp.expand); rk=DM(B2H).rank()
    random.seed(r); g=0
    for _ in range(4):
        U=sp.Matrix(rk,H.rows,lambda i,j: random.randint(-3,3)); d=DM(U*B2H*U.T,R).det().as_expr(); g=sp.gcd(g,d) if g!=0 else d
    W=polybasis(DM(B2H).nullspace().to_Matrix()); Wv=(W*H).applyfunc(sp.expand)
    B3W=(Wv*B3*Wv.T).applyfunc(sp.factor); r3=DM(B3W).rank()
    e3=0
    for x in B3W:
        if x!=0: e3=sp.gcd(e3,sp.expand(x)) if e3!=0 else sp.expand(x)
    w1=polybasis(DM(B3W).nullspace().to_Matrix()); wp=(w1*Wv).applyfunc(sp.expand)
    qq=sp.factor((wp*q0*wp.T)[0,0])
    def degen(Mb):
        g_=0
        for cc in itertools.combinations(range(Mb.cols),Mb.rows):
            x=sp.expand(Mb.extract(list(range(Mb.rows)),list(cc)).det())
            if x!=0: g_=sp.gcd(g_,x) if g_!=0 else x
        return sp.factor(g_)
    print('   basis degeneracies: H',degen(H),'| W (in H coords)',degen(W),'| w\' (in W coords)',degen(w1),'| ell_j vanishes where all entries of B1 row %d vanish:'%r,sp.factor(sp.gcd_list([sp.expand(x) for x in ell if x!=0])),flush=True)
    print('branch B1 row %d: dim H %d | rank B2|H %d (drops only on V(%s)) | rank B3|W %d (vanishes only on V(%s)) | q0(w\',w\') = %s'%(r,H.rows,rk,sp.factor(g),r3,sp.factor(e3),qq),flush=True)
