# random members of the exact NC family M(w0,w1,w3): invariants (numerical).
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
import numpy as np
from t import *
from a1 import embed, defect
from a5 import onb
from a6 import T1, E0
from r5_FO2 import FO2
from fam_nc import fam
rg=np.random.default_rng(5); cnt={}
for trial in range(10):
    w0=rg.normal(size=4)+1j*rg.normal(size=4); w0-=w0.mean()
    # plane P = {w : sum w = 0, w.w0 = 0}
    A=np.array([np.ones(4),w0]); P=null(A)        # rows p,q with A p = 0 (bilinear)
    p,q=P[0],P[1]; G=np.array([[p@p,p@q],[q@p,q@q]])
    def w13(th):
        c1=np.array([1,th]); w1=c1[0]*p+c1[1]*q
        g=G@c1; c3=np.array([-g[1],g[0]]); w3=c3[0]*p+c3[1]*q      # w3.w1 = c3^T G c1 = 0
        return w1,w3
    f=lambda th:(w0*w13(th)[0]*w13(th)[1]).sum()
    ths=np.array([0,1,-1]); co=np.polyfit(ths,[f(t) for t in ths],2); th=np.roots(co)[trial%2]
    w1,w3=w13(th); B=onb(fam(w0,w1,w3))
    le=level_err(B,ntest=50); T=T1(embed(B),rg,npts=130); S=np.linalg.svd(T[:,4,:],compute_uv=False)
    key=(int((defect(B)>1e-8).sum()),len(T),int((S>1e-8).sum()),FO2(embed(B),rg)[2],len(E0(B,rg)))
    cnt[key]=cnt.get(key,0)+1
    if le>1e-9: print('member not level?',le)
print('random members of the NC family: (e, dim T1, dim Omega, FO2 bound, dim E0) -> count:',cnt)
