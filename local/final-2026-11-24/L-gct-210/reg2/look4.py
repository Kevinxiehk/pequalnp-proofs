import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from t import *
from a1 import embed, defect, phirank
from a5 import onb, rref_tol
from a6 import T1, E0
from r5_FO2 import FO2, cof55
from show import rref
np.set_printoptions(precision=3,suppress=True,linewidth=200)
rg=np.random.default_rng(4)
f=sys.argv[1]; B0=onb(np.load(f))
def gsv(B):
    Mb=embed(B).reshape(len(B),25); rows=[]
    for _ in range(120):
        c=rg.normal(size=len(B))+1j*rg.normal(size=len(B)); rows.append(cof55(np.ones((5,5))+(c@Mb).reshape(5,5)))
    return np.linalg.svd(np.array(rows),compute_uv=False)
s=gsv(B0); print('raw: gradient-span sv (tail):',np.array2string(s[10:20]/s[0],precision=2))
for tol in (1e-5,1e-4):
    R=rref_tol(B0,tol); B=onb(R); le=level_err(B,ntest=200,seed=3)
    s=gsv(B); print('rounded at %.0e: level err %.1e ; gradient-span sv tail %s'%(tol,le,np.array2string(s[10:20]/s[0],precision=2)))
R=rref_tol(B0,1e-5); B=onb(R)
if level_err(B,ntest=200,seed=3)<1e-9:
    np.save(f.replace('.npy','_lim.npy'),B)
    T=T1(embed(B),rg,npts=120); U,S2,Vh=np.linalg.svd(T[:,4,:].T,full_matrices=False); r=int((S2>1e-7*S2[0]).sum())
    print('LIMIT space: dim T1',len(T),'dim Omega',r,'dim E0',len(E0(B,rg)),'FO2',FO2(embed(B),rg),'defect sv',np.array2string(defect(B,n=60),precision=2),'Phi sv',np.array2string(phirank(B),precision=2))
    Rr,_=rref(U[:,:r].T.reshape(r,1,5)); print('Omega (rref):'); print(Rr.reshape(r,5))
    print('single-row parts',[len(rowpart(B,[i])) for i in range(4)],'single-col parts',[len(colpart(B,[j])) for j in range(5)])
    for m in R: print(np.array2string(m,precision=3,suppress_small=True)); print()
