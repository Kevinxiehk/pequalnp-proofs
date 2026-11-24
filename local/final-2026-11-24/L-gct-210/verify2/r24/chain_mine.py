# verify2 r24/25: my own pointwise recursive-kernel-bound check (lemmas L1, L2) at rational parameter values.
# usage: python3 -I chain_mine.py CACHE "i1,i2,..." (chain order of form indices into Gs; Gs[0] = q0) "p1;p2;..." (values of the single parameter)
import pickle, sys, sympy as sp, random
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(sys.argv[1],'rb'))
order=[int(x) for x in sys.argv[2].split(',')]; vals=[sp.Rational(v) for v in sys.argv[3].split(';')] if par else [None]
print('cache',sys.argv[1].split('/')[-1],'par',par,'nq',nq,'#forms',len(Gs),'fix',fix,'dens',dens)
for v in vals:
    G=[g.subs(par[0],v) if par else g for g in Gs]
    W=sp.eye(nq); m=4; log=[]
    for i in order:
        R=W.T*G[i]*W; r=R.rank(); N=R.nullspace()
        m=m-r//2; W=W*sp.Matrix.hstack(*N) if N else sp.zeros(nq,0); log.append('B%d|rank %d -> dim %d need %d'%(i,r,W.shape[1],m))
        if W.shape[1]==0: break
    d=W.shape[1]
    random.seed(3); comb=sum((random.randint(1,97)*(W.T*g*W) for g in G),sp.zeros(d)) if d else sp.zeros(0)
    rho=comb.rank() if d else 0; mx=(d-rho)+rho//2
    print(' param=%s: %s ; generic combination rank %d on dim %d -> max isotropic %d, need %d => %s'%(v,' > '.join(log),rho,d,mx,m,'KILL' if m>mx else 'NOT decided'))
