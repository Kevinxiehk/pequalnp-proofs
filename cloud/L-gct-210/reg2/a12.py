import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2'); sys.path.insert(0,'/home/claude/work/L-gct-210/chief')
import numpy as np, glob
from t import *
from a1 import embed, defect, phirank
from a5 import onb
from a6 import T1, E0
from a9 import Omega
from a10 import Lr
from r5_FO2 import FO2
import core
np.set_printoptions(precision=3,suppress=True,linewidth=200)
rg=np.random.default_rng(3)
for name in core.SP:
    B=np.array([np.array(m,dtype=complex) for m in core.SP[name]()])
    for tr,Bt in (('row',B),('col',B.transpose(0,2,1))):
        for r in range(5):
            M=Lr(Bt,r)
            if len(M)!=6: continue
            M=onb(M); W=Bt[:,r,:]; u,s,vh=np.linalg.svd(W); z=vh[0].conj() if False else None
            U,S,Vh=np.linalg.svd(W.T,full_matrices=False); z=U[:,0]; z=z/z[np.argmax(abs(z))]
            n,rho,bd=FO2(embed(M),rg); Om,nT=Omega(M,rg)
            print('%-10s %s %d: srow %s scol %s e=%d Om=%d T1=%d rk=%d FO2=%d  W_r spanned by %s'%(name,tr,r,[len(rowpart(M,[i])) for i in range(4)],[len(colpart(M,[j])) for j in range(5)],int((defect(M)>1e-6).sum()),len(Om),n,rho,bd,np.array2string(z,precision=3,suppress_small=True)))
