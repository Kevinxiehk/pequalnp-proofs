# pattern (3,1|2), the only incidence case not covered by SP8 (hand, NOTES-reg2 section 9.4):
#   M(m) = e_0 (x) {w : sum w = 0, <m,w> = 0} (+) C e_1 m^T (+) {x e_4^T : x_0 = 0, sum x = 0},  m = (m_0..m_3, 0), sum m = 0.
#   level for EVERY such m (hand); SP8 covers m non-isotropic and m = e_a - e_b; here: isotropic m.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from t import *
from a1 import embed, defect
from a5 import onb
from a6 import T1, E0
from r5_FO2 import FO2
def fam(m):
    m=np.array(m,complex); K=null(np.array([np.ones(5),m]))      # rows: basis of {1,m}^perp (bilinear)
    B=np.zeros((6,4,5),complex)
    for k in range(3): B[k,0]=K[k]
    B[3,1]=m; B[4,1,4]=1; B[4,2,4]=-1; B[5,2,4]=1; B[5,3,4]=-1
    return B
rg=np.random.default_rng(0); w=np.exp(2j*np.pi/3)
def iso4(t):            # isotropic sum-zero vectors on coordinates 0..3: rational parametrisation of the conic
    # m = (1, i, -1, -i) type family: solve with m0=1, m1=t, m2, m3 from sum=0, sumsq=0
    s=-1-t; q=1+t*t      # m2+m3 = s, m2^2+m3^2 = -q -> m2*m3 = (s^2+q)/2
    p=(s*s+q)/2; disc=np.sqrt(s*s-4*p+0j); return [1,t,(s+disc)/2,(s-disc)/2,0]
cases={'iso (1,i,-1,-i,0)':[1,1j,-1,-1j,0],'iso (1,w,w2,0,0)':[1,w,w*w,0,0],'iso t=0.3':iso4(0.3),'iso t=2+i':iso4(2+1j),
       'noniso generic':[1,2,-0.5,-2.5,0],'two-col (1,-1,0,0,0)':[1,-1,0,0,0]}
for k,m in cases.items():
    m=np.array(m,complex); Bo=onb(fam(m)); T=T1(embed(Bo),rg,npts=160); U_,S,Vh=np.linalg.svd(T[:,4,:].T,full_matrices=False); r=int((S>1e-8*S[0]).sum())
    fo=FO2(embed(Bo),np.random.default_rng(1),npts=160)
    print('%-22s <m,m>=%.1e lev %.0e e=%d dimE0=%d dimT1=%d dimOmega=%d FO2=%s'%(k,abs(m@m),level_err(Bo,ntest=30),int((defect(Bo)>1e-8).sum()),len(E0(Bo,rg,npts=160)),len(T),r,fo),flush=True)
