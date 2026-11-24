# verify2 r25: my own pointwise check of the J_A^R1 kill (stage2 R21-1): rank-2 split of B1 + recursive kernel bound in each hyperplane.
import pickle, sympy as sp, random, itertools
d=pickle.load(open('/home/kevxhk/work/L-gct-210/stage2/r16/cache_ad03c283c2b2.pkl','rb'))
par,Gs,nq,fix=d[5],d[6],d[8],d[12]; lam,a3=par
def kill_in(W,G,m,depth=0):
    """DFS recursive bound inside span(W); True if contradiction found"""
    dW=W.shape[1]
    if dW==0: return m>0
    random.seed(5); comb=sum((random.randint(1,97)*(W.T*g*W) for g in G),sp.zeros(dW)); rho=comb.rank()
    if m>(dW-rho)+rho//2: return True
    if depth>=6: return False
    for g in G:
        R=W.T*g*W; r=R.rank()
        if r==0: continue
        N=R.nullspace(); W2=W*sp.Matrix.hstack(*N) if N else sp.zeros(nq,0)
        if kill_in(W2,G,m-r//2,depth+1): return True
    return False
for lv,av in [(sp.Rational(2,3),sp.Rational(5,7)),(sp.Rational(-4,5),sp.Rational(3,2)),(sp.Rational(7,2),sp.Rational(-9,4))]:
    G=[g.subs({lam:lv,a3:av}) for g in Gs]
    B1=G[1]; r1=B1.rank()
    # factor rank-2 symmetric B1 = x y^T + y x^T: take its 2-dim column space, restrict, diagonalise the 2x2 form to find the two isotropic lines
    C=sp.Matrix.hstack(*B1.columnspace()); 
    # B1 = C S C^T for the 2x2 S: solve via pseudo-inverse
    S=(C.T*C).inv()*C.T*B1*C*(C.T*C).inv()
    # isotropic directions of S: S = [[p,q],[q,r]]; the linear forms l1, l2 are C*(root vectors) with S ~ l1 l2 (needs det S < 0 square class OK over Qbar)
    p,q,r=S[0,0],S[0,1],S[1,1]; t=sp.Symbol('t'); roots=sp.solve(p*t**2+2*q*t+r,t)
    res=[]
    for rt in roots:
        # isotropic vector (rt,1) of S; the hyperplane H = {x : (C^T x) is S-orthogonal... } -- simpler: B1 = l1 l2 sym, l_i = rows of the factorisation
        pass
    # Direct: B1(x,x) = l1(x) l2(x). Find l1, l2 by factoring the quadratic form over the algebraic closure:
    X=sp.symbols('x0:%d'%nq); Qf=sp.expand((sp.Matrix([X]) * B1 * sp.Matrix(X))[0])
    fac=sp.factor_list(Qf, extension=sp.sqrt(sp.discriminant(p*t**2+2*q*t+r,t)) if sp.discriminant(p*t**2+2*q*t+r,t)!=0 else None)
    lins=[f for f,e in fac[1] if sp.Poly(f,*X).total_degree()==1]
    out=[]
    for lf in lins:
        coeffs=sp.Matrix([[sp.Poly(lf,*X).coeff_monomial(x) for x in X]])
        H=sp.Matrix.hstack(*coeffs.nullspace())
        out.append(kill_in(H,G,4))
    print('lam=%s a3=%s: rank B1 %d, factors %d linear, kill in each hyperplane: %s'%(lv,av,r1,len(lins),out))
