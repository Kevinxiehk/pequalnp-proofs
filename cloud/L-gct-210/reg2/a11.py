import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2'); sys.path.insert(0,'/home/claude/work/L-gct-210/chief')
import numpy as np, glob
from t import *
from a1 import embed, defect, phirank
from a5 import onb
from a6 import T1, E0
from a9 import Omega
from a10 import Lr
from r5_FO2 import FO2
from show import rref
import core
np.set_printoptions(precision=3,suppress=True,linewidth=200)
rg=np.random.default_rng(3)
cases=[('L080','col',0),('ex2','row',4),('ex3','row',4),('fam2','row',4),('ex1','row',4),('L080','row',0)]
saved={}
for name,tr,r in cases:
    B=np.array([np.array(m,dtype=complex) for m in core.SP[name]()]); Bt=B if tr=='row' else B.transpose(0,2,1)
    M=onb(Lr(Bt,r)); saved[(name,tr,r)]=M
    n,rho,bd=FO2(embed(M),rg); E=E0(M,rg); Om,nT=Omega(M,rg)
    print('%s %s %d: dim %d lev %.0e srow %s scol %s rowrk %s colrk %s e=%d PhiRk=%d E0=%d T1=%d rk=%d FO2=%d Om=%d'%(name,tr,r,len(M),level_err(M),[len(rowpart(M,[i])) for i in range(4)],[len(colpart(M,[j])) for j in range(5)],[rank(M[:,i,:]) for i in range(4)],[rank(M[:,:,j]) for j in range(5)],int((defect(M)>1e-6).sum()),int((phirank(M)>1e-6).sum()),len(E),n,rho,bd,len(Om)))
np.save('M_L080_col0.npy',saved[('L080','col',0)]); np.save('M_ex2_row4.npy',saved[('ex2','row',4)])
R,_=rref(saved[('L080','col',0)])
for m in R: print(m.real if abs(m.imag).max()<1e-9 else m); print()
