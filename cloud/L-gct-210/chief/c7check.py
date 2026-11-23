import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/chief')
import numpy as np
from core import nullspace
from testAB_lib import rank, Qf
rng=np.random.default_rng(2)
def PiT(kap,kapp,nu,nup,j,l):
    # z=(z1j,z1l,z2j,z2l): constraints <kap,z1>-<kapp,z2>=0, <nu,z1>+<nup,z2>=0 ; ordering for Qf: (11,12,21,22)
    A=np.array([[kap[j],kap[l],-kapp[j],-kapp[l]],[nu[j],nu[l],nup[j],nup[l]]])
    N=nullspace(A); ell=np.array([kap[j],kap[l],0,0])@N
    return N,ell
def rk_q(N): return rank(N.T@Qf@N,1e-9)
def rnd(k): return rng.normal(size=k)+1j*rng.normal(size=k)
j,l=0,1
res={}
# generic: expect rank 2 (violates B1)
kap,kapp=rnd(5),rnd(5); rho,rhop=rnd(5),rnd(5); nu,nup=rho*kap,rhop*kapp
N,ell=PiT(kap,kapp,nu,nup,j,l); res['generic']=(N.shape[1],rk_q(N),abs(ell).max()>1e-9)
# rho_j=rho_l only: expect rank 2 unless omega_j sigma_j+omega_l sigma_l=0
rho2=rho.copy(); rho2[l]=rho2[j]; nu2=rho2*kap
N,ell=PiT(kap,kapp,nu2,nup,j,l); res['rho equal, no relation']=(N.shape[1],rk_q(N),abs(ell).max()>1e-9)
# impose relation: omega_j sigma_j + omega_l sigma_l = 0 by solving for rhop[l]
om=kapp/kap; sj=rho2[j]+rhop[j]; rhop3=rhop.copy(); rhop3[l]=-om[j]*sj/om[l]-rho2[l]
N,ell=PiT(kap,kapp,nu2,rhop3*kapp,j,l); res['rho equal + (R1)']=(N.shape[1],rk_q(N),abs(ell).max()>1e-9)
# rho' equal only + (R1'): omega_l sigma_j + omega_j sigma_l = 0
rhop4=rhop.copy(); rhop4[l]=rhop4[j]; rho4=rho.copy(); sj=rho4[j]+rhop4[j]; rho4[l]=-om[l]*sj/om[j]-rhop4[l]
N,ell=PiT(kap,kapp,rho4*kap,rhop4*kapp,j,l); res["rho' equal + (R1')"]=(N.shape[1],rk_q(N),abs(ell).max()>1e-9)
# both separated with omega_j+omega_l=0: D_T=0 : kernel isotropic but radical condition extra -> generic rank 2
kapp5=kapp.copy(); kapp5[l]=-kapp[j]*kap[l]/kap[j]
N,ell=PiT(kap,kapp5,rho*kap,rhop*kapp5,j,l); res['separated, D_T=0']=(N.shape[1],rk_q(N),abs(ell).max()>1e-9)
# both equal: sigma_j=sigma_l !=0 -> ell==0 on Pi_T, dim 2
rho6=rho.copy(); rho6[l]=rho6[j]; rhop6=rhop.copy(); rhop6[l]=rhop6[j]
N,ell=PiT(kap,kapp,rho6*kap,rhop6*kapp,j,l); res['both equal']=(N.shape[1],rk_q(N),abs(ell).max()>1e-9)
for k,v in res.items(): print('%-28s dim Pi_T=%d  rank q_T|Pi=%d  ell!=0 on Pi: %s'%(k,v[0],v[1],v[2]))
