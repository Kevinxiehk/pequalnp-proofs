# Scan of dim T_1(M*) over the parameters (m_a, m_b, al, be, ga) of M*: integer grid samples (float rank with a safe tolerance, plus exact
# Fraction rank on a subsample) and random complex parameters.
import sys, random, itertools, numpy as np
from collections import Counter
sys.argv=[sys.argv[0]]
src=open('/home/kevxhk/work/L-gct-210/stage2/r4_Mstar_ext.py').read().split("random.seed(3)")[0]
exec(src)
random.seed(7); rg=np.random.default_rng(7)
def cofspan_rank(basis,npts=45,cplx=False):
    rows=[]
    for trial in range(npts):
        co=rg.normal(size=6)+(1j*rg.normal(size=6) if cplx else 0)
        M=np.ones((5,5),dtype=complex)+sum(co[k]*np.array(basis[k],dtype=complex) for k in range(6))
        rows.append(cof(M.tolist()))
    s=np.linalg.svd(np.array(rows),compute_uv=False); return int((s>1e-8*s[0]).sum()), s[16]/s[0], (s[17]/s[0] if len(s)>17 else 0)
cnt=Counter(); worst=1
for trial in range(300):
    ma,mb=random.randint(-5,5),random.randint(-5,5); al,be,ga=[random.choice([-5,-4,-3,-2,-1,1,2,3,4,5]) for _ in range(3)]
    rk,s17,s18=cofspan_rank(Mstar(ma,mb,al,be,ga)); cnt[rk]+=1; worst=min(worst,s17)
print('integer parameters, 300 samples: rank of the cofactor span -> count',dict(cnt),' smallest relative 17th singular value %.1e'%worst)
cnt=Counter(); worst=1
for trial in range(100):
    par=list(rg.normal(size=5)+1j*rg.normal(size=5)); rk,s17,s18=cofspan_rank(Mstar(*par),cplx=True); cnt[rk]+=1; worst=min(worst,s17)
print('complex parameters, 100 samples: rank -> count',dict(cnt),' smallest relative 17th singular value %.1e'%worst)
# special loci
for par in ((0,0,1,1,1),(1,1,1,1,1),(1,-1,1,1,1),(0,1,1,1,1),(1,0,1,-1,1),(1,2,1,1,-1),(3,3,1,2,2),(1,-1,1,-1,-1),(2,-2,1,1,2)):
    rk,s17,s18=cofspan_rank(Mstar(*par)); print(' special',par,' rank',rk)
