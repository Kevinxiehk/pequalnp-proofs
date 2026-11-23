import numpy as np, sys
sys.path.insert(0,'.')
from core import *; from c35 import iota, Eperp, W
rng=np.random.default_rng(5)
xs=[to_mat(rng.normal(size=(1,24))+1j*rng.normal(size=(1,24))) for _ in range(4)]
X=[iota(x)[0] for x in xs]
Gm=(Eperp*W)@Eperp.T  # tr_w gram on E^perp
def eproj(v):  # E^perp component of v (tr_w-orthogonal projection)
    c=np.linalg.solve(Gm,(Eperp*W)@v); return c@Eperp
x,y,z,w=X
lhs=Qf(prod(xs[0],xs[1]),prod(xs[2],xs[3]))[0]
S4=(W*x*y*z*w).sum(); ee=(W*eproj(x*y)*eproj(z*w)).sum()
print(lhs, S4-ee)
# covariance description: tr_w(x y e) for e in E^perp basis
e=Eperp[3]; print((W*x*y*e).sum())
