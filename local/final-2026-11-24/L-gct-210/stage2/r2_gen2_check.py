# Sanity for the isotropy step of (GEN-3): for Type I / Type II pair data (zero-free), a 4-subset Sigma (Sigma^c = {d}) and
# I^d := {z in I^_12 : z_1d = z_2d = 0}, is there a nonzero symmetric zero-diagonal 4x4 matrix B with z_1^T B z_2 = 0 on I^d ?
# Claim: never (Type I: needs sigma_0 = 0; Type II: needs y = -1 or B of rank <= 1).  Exact linear algebra in floats (tiny systems).
import sys, itertools, numpy as np; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from pairlib import nullspace, rank, typeI
rng=np.random.default_rng(13)
def rnd(k): return rng.normal(size=k)+1j*rng.normal(size=k)
def dimB(kap,kapp,nu,nup,d):
    Sig=[j for j in range(5) if j!=d]
    A=np.array([np.concatenate([kap[Sig],-kapp[Sig]]),np.concatenate([nu[Sig],nup[Sig]])])
    N=nullspace(A)                       # basis of I^d inside C^{2 x Sigma} (8 x 6)
    pairs=list(itertools.combinations(range(4),2)); rows=[]
    # unknown B entries b_p (6); condition: for basis vectors n_a, n_b of I^d: polarised form vanishes
    for a in range(N.shape[1]):
        for b in range(a,N.shape[1]):
            za=N[:,a]; zb=N[:,b]; row=[]
            for (j,l) in pairs:
                row.append(za[j]*zb[4+l]+za[l]*zb[4+j]+zb[j]*za[4+l]+zb[l]*za[4+j])
            rows.append(row)
    return 6-rank(np.array(rows)), N.shape[1]
out={}
for eps in itertools.product([1,-1],repeat=5):
    if eps[0]!=1 or abs(sum(eps)) not in (1,):   # block sizes (2,3) only (GEN-0)
        continue
    kap=rnd(5); kap/=kap.sum(); kapp,nu,nup,c,s0=typeI(kap,eps)
    for d in range(5):
        k=dimB(kap,kapp,nu,nup,d); out[('I',k)]=out.get(('I',k),0)+1
for cells in itertools.product(range(3),repeat=5):
    if len(set(cells))<3: continue
    for e in (1,-1):
        cells_=np.array(cells); kap=rnd(5); kap/=kap.sum()
        w=np.where(cells_==0,e*1j,np.where(cells_==1,1,-1)).astype(complex); cc=1/(w*kap).sum(); kapp=cc*w*kap
        y=(-1+e*1j)/2; nu=kap*(cells_==2); nup=np.where(cells_==1,y+1,y)*kapp
        for d in range(5):
            k=dimB(kap,kapp,nu,nup,d); out[('II',k)]=out.get(('II',k),0)+1
print('(type,(dim of admissible B, dim I^d)) -> count:',out)
