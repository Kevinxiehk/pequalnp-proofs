# numerical invariants of pattern (2,1,1|2) case (iii): mu = (0,1,m3,m4) (generator reg2/gb/gen_dr211.py)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from t import *
from a1 import embed, defect
from a5 import onb
from a6 import T1, E0
from r5_FO2 import FO2
def fam(m3,m4):
    S=1+m3+m4; B=np.zeros((6,4,5),complex)
    B[0,0,1:]=[m3-1,-m3,1,0]; B[1,0,1:]=[m4-1,-m4,0,1]; B[2,1]=[4,-1,-1,-1,-1]
    B[3,2,1:]=[-S,4-S,4*m3-S,4*m4-S]; B[4,0,0]=1; B[4,2,0]=-1; B[5,2,0]=1; B[5,3,0]=-1
    return B
rg=np.random.default_rng(0)
for (m3,m4) in [(0.3+0.2j,-1.1),(2,3),(0,0),(1,1),(0,1),(1,0),(-1,0),(2,-1),(0.5,0.5),(-1,-1)]:
    Bo=onb(fam(m3,m4)); T=T1(embed(Bo),rg,npts=160); U_,S,Vh=np.linalg.svd(T[:,4,:].T,full_matrices=False); r=int((S>1e-8*S[0]).sum())
    fo=FO2(embed(Bo),np.random.default_rng(1),npts=160)
    print('m3,m4=%-14s lev %.0e e=%d dimE0=%d dimT1=%d dimOmega=%d FO2=%s'%((m3,m4),level_err(Bo,ntest=30),int((defect(Bo)>1e-8).sum()),len(E0(Bo,rg,npts=160)),len(T),r,fo),flush=True)
