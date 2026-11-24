# numeric check: my tau-form of Type II passes the ThB pair test
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from pairlib import *
rng=np.random.default_rng(3)
def rnd(k): return rng.normal(size=k)+1j*rng.normal(size=k)
bad=0; n=0
for cells in itertools.product(range(3),repeat=5):
    if len(set(cells))<3: continue
    for eps in (1,-1):
        cells=np.array(cells); kap=rnd(5); kap/=kap.sum()
        w=np.where(cells==0,eps*1j,np.where(cells==1,1,-1)).astype(complex)
        c=1/(w*kap).sum(); kapp=c*w*kap
        y=(-1+eps*1j)/2
        nu=kap*(cells==2); rhop=np.where(cells==1,y+1,y); nup=rhop*kapp
        ok,out=pair_check(kap,kapp,nu,nup); n+=1
        if not ok: bad+=1
        # opposite sign of y must fail
        if n<=3:
            y2=(-1-eps*1j)/2; ok2,_=pair_check(kap,kapp,nu,np.where(cells==1,y2+1,y2)*kapp); print('wrong-sign control passes?',ok2)
print('Type II structures tested:',n,' failures:',bad)
