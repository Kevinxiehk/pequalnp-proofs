# sanity for the two zero-entry consequences (Z-0), (Z-1) of the pair criterion
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from pairlib import *
rng=np.random.default_rng(9)
def rnd(k): return rng.normal(size=k)+1j*rng.normal(size=k)
def Tok(kap,kapp,nu,nup,T):
    ok,out=pair_check(kap,kapp,nu,nup); return [o[4] for o in out if o[0]==T][0]
# (Z-0): column 0 with kappa=kappa'=nu=nu'=0 ; another column l with kappa_l kappa'_l != 0  -> T={0,l} must FAIL
kap=rnd(5); kapp=rnd(5); nu=rnd(5); nup=rnd(5)
for v in (kap,kapp,nu,nup): v[0]=0
print('(Z-0) T={0,1} passes with kappa_1 kappa\'_1 != 0 ?',Tok(kap,kapp,nu,nup,(0,1)))
k2=kapp.copy(); k2[1]=0; print('(Z-0) T={0,1} passes with kappa\'_1 = 0 ?',Tok(kap,k2,nu,nup,(0,1)))
# (Z-1): column 0 with kappa=kappa'=0, (nu_0,nu'_0) != 0: T={0,l} passes iff nu'_0/nu_0 = kappa'_l/kappa_l and sigma_l != 0
kap=rnd(5); kapp=rnd(5); nu=rnd(5); nup=rnd(5); kap[0]=0; kapp[0]=0
print('(Z-1) generic: T={0,1} passes ?',Tok(kap,kapp,nu,nup,(0,1)))
nup2=nup.copy(); nup2[0]=nu[0]*kapp[1]/kap[1]
print('(Z-1) with nu\'_0/nu_0 = omega_1: T={0,1} passes ?',Tok(kap,kapp,nu,nup2,(0,1)),' T={0,2} passes ?',Tok(kap,kapp,nu,nup2,(0,2)))
nu3=nu.copy(); nu3[1]=-nup2[1]*kap[1]/kapp[1]   # sigma_1 = 0
print('(Z-1) same but sigma_1 = 0: T={0,1} passes ?',Tok(kap,kapp,nu3,nup2,(0,1)))
