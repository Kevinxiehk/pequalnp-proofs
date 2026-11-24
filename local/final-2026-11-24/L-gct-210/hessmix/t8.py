import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/hessmix')
from hk import *
rng=np.random.default_rng(2)
def Phi(x):
    m,a_,b_,g=parts(x); return g-1.5*ab(a_,b_)
err=0
for _ in range(5):
    t=rng.normal(size=(5,5))+1j*rng.normal(size=(5,5)); t-=t.mean()
    u=Phi(t); R=u.sum(1); C=u.sum(0)
    P=Pk(t)[0]
    e2=abs(2*P[2]-((u*u).sum()-(5/9)*((R*R).sum()+(C*C).sum())))
    e3=abs(P[3]-(2/3)*((u**3).sum()-(1/9)*((R**3).sum()+(C**3).sum())))
    err=max(err,e2,e3)
print('max err P2,P3 in u-coords (sum-zero t):',err)
# P4 check: is P4 = c*(p4(u) - w4(sum R^4 + sum C^4)) + other? test on DC (R=C=0): known not pure p4
