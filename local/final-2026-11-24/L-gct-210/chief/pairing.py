import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief')
from core import *
from testAB_lib import hat
from rho import p2,p3,pairs,trip
rng=np.random.default_rng(11)
for name in ('ex1','L080','fam.6+1.4i','K5'):
    Bh=hat(SP[name]()); m=len(Bh); worst=0
    for _ in range(5):
        cu=rng.normal(size=m)+1j*rng.normal(size=m); cv=rng.normal(size=m)+1j*rng.normal(size=m)
        u=np.tensordot(cu,Bh,1); v=np.tensordot(cv,Bh,1)
        s=0
        for S in pairs:
            Sc=[i for i in range(5) if i not in S]
            for T in pairs:
                Tc=[j for j in range(5) if j not in T]
                s+=p2(u[np.ix_(S,T)])*p3(v[np.ix_(Sc,Tc)])
        worst=max(worst,abs(s-1200*cu[0]**2*cv[0]**3)/(1+abs(1200*cu[0]**2*cv[0]**3)))
    print(name,'pairing identity rel err %.1e'%worst)
