# verify2 r24: my own pointwise check of the recursive kernel bound on R2 line (0,0,0) at random rational nu (stage2 R21-2).
import pickle, sympy as sp, random
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open('/home/kevxhk/work/L-gct-210/stage2/r16/cache_0d3623f0f596.pkl','rb'))
print('params',par,'nq',nq,'fix',fix)
for nv in (sp.Rational(2,7),sp.Rational(-5,11),sp.Rational(13,3)):
    G=[g.subs(nu,nv).applyfunc(sp.nsimplify) for g in Gs]
    q0,B1,B2,B3=G
    K1=sp.Matrix.hstack(*B1.nullspace())            # ker B1
    r1=B1.rank(); 
    B2r=K1.T*B2*K1; K2=sp.Matrix.hstack(*B2r.nullspace()); W=K1*K2   # ker of B2 restricted to ker B1
    need=4-r1//2; need2=need-B2r.rank()//2
    forms=[K.T*M*K for K in [W] for M in (q0,B1,B2,B3)]
    random.seed(1); comb=sum((random.randint(1,50)*f for f in forms),sp.zeros(W.shape[1]))
    rho=comb.rank(); d=W.shape[1]; maxiso=(d-rho)+rho//2
    print('nu=%s: rank B1 %d (ker dim %d, need %d) ; rank B2|kerB1 %d -> W dim %d, need %d ; generic combination rank %d -> max isotropic %d => %s'
          %(nv,r1,K1.shape[1],need,B2r.rank(),d,need2,rho,maxiso,'KILL' if need2>maxiso else 'no'))
