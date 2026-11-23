import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
from pairlib import *
rng=np.random.default_rng(5)
def rnd(k): return rng.normal(size=k)+1j*rng.normal(size=k)
# 1. generic annihilators violate
kap=rnd(5); kap/=kap.sum(); kapp=rnd(5); kapp/=kapp.sum(); nu=rnd(5); nup=rnd(5); nup-= (nu.sum()+nup.sum())/5
ok,out=pair_check(kap,kapp,nu,nup); ok2,_=gamma_check(kap,kapp,nu,nup); print('generic: pair_check',ok,' gamma_check',ok2)
# 2. Type I for all sign patterns
cnt=0; bad=0
for eps in itertools.product([1,-1],repeat=5):
    if eps[0]!=1 or abs(sum(eps))==5: continue
    kap=rnd(5); kap/=kap.sum(); kapp,nu,nup,c,s0=typeI(kap,eps)
    assert abs(kapp.sum()-1)<1e-9 and abs(nu.sum()+nup.sum())<1e-9
    ok,out=pair_check(kap,kapp,nu,nup); ok2,_=gamma_check(kap,kapp,nu,nup); cnt+=1
    if not (ok and ok2): bad+=1; print('TypeI FAIL',eps,out)
print('Type I: %d sign patterns, failures %d'%(cnt,bad))
# 3. agreement of the two criteria on random special data (zeros / equalities)
agree=0; tot=0; passed=0
for trial in range(4000):
    kap=rnd(5); kapp=rnd(5); nu=rnd(5); nup=rnd(5)
    # random degenerations
    for v in (kap,kapp,nu,nup):
        m=rng.random(5)<0.35; v[m]=0
    if rng.random()<0.5:
        j,l=rng.choice(5,2,replace=False); nu[l]=nu[j]*kap[l]/kap[j] if abs(kap[j])>0 else nu[l]
    if abs(kap.sum())<1e-6 or abs(kapp.sum())<1e-6: continue
    kap/=kap.sum(); kapp/=kapp.sum()
    ok,_=pair_check(kap,kapp,nu,nup); ok2,_=gamma_check(kap,kapp,nu,nup); tot+=1; agree+= (ok==ok2); passed+=ok
print('criteria agree on %d of %d degenerate random data (passing: %d)'%(agree,tot,passed))
