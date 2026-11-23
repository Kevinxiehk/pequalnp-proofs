# Sanity for two linear-algebra claims of Theorem GEN-2 / Lemma GEN-3 on Type I ((2,3) blocks) and all Type II pair data:
#  (a) for every column pair {d,e}: the four functionals z_1d, z_1e, z_2d, z_2e are independent on I^_12  (dim of {z in I^: block = 0} is 4)
#  (b) for every column d: z_1d, z_2d independent on I^_12 and I^d has codim exactly 2 in C^{2 x Sigma}.
import sys, itertools, numpy as np; sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
from pairlib import nullspace, rank, typeI
rng=np.random.default_rng(17)
def rnd(k): return rng.normal(size=k)+1j*rng.normal(size=k)
def chk(kap,kapp,nu,nup):
    A=np.array([np.concatenate([kap,-kapp]),np.concatenate([nu,nup])]); I=nullspace(A)   # 10 x 8
    ok=True
    for d,e in itertools.combinations(range(5),2):
        ok&= rank(I[[d,e,5+d,5+e],:])==4
    for d in range(5):
        ok&= rank(I[[d,5+d],:])==2
    return ok
nI=bI=nII=bII=0
for eps in itertools.product([1,-1],repeat=5):
    if eps[0]!=1 or abs(sum(eps))!=1: continue
    kap=rnd(5); kap/=kap.sum(); kapp,nu,nup,c,s0=typeI(kap,eps); nI+=1; bI+= (not chk(kap,kapp,nu,nup))
for cells in itertools.product(range(3),repeat=5):
    if len(set(cells))<3: continue
    for e in (1,-1):
        cells_=np.array(cells); kap=rnd(5); kap/=kap.sum()
        w=np.where(cells_==0,e*1j,np.where(cells_==1,1,-1)).astype(complex); cc=1/(w*kap).sum(); kapp=cc*w*kap
        y=(-1+e*1j)/2; nu=kap*(cells_==2); nup=np.where(cells_==1,y+1,y)*kapp
        nII+=1; bII+= (not chk(kap,kapp,nu,nup))
print('Type I (2,3)-partitions: %d, failures %d ;  Type II structures: %d, failures %d'%(nI,bI,nII,bII))
