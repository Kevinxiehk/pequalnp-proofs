# numerical invariants of members of the DR2 family (2,2|2):  mu = (0,1,m3,m4)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from t import *
from a1 import embed, defect, phirank
from a5 import onb
from a6 import T1, E0
from r5_FO2 import FO2
from show import rref
np.set_printoptions(precision=3,suppress=True,linewidth=200)
def fam22(m3,m4):
    S=1+m3+m4; B=np.zeros((6,4,5),complex)
    B[0,0,1:]=[m3-1,-m3,1,0]; B[1,0,1:]=[m4-1,-m4,0,1]
    B[2,1]=[4,-1,-1,-1,-1]; B[3,1]=[-S,-S,5-S,5*m3-S,5*m4-S]
    B[4,0,0]=1; B[4,2,0]=-1; B[5,2,0]=1; B[5,3,0]=-1
    return B
rg=np.random.default_rng(0)
for name,(m3,m4) in (('generic (0.3+0.2i, -1.1)',(0.3+0.2j,-1.1)),('generic (2, 3)',(2,3)),('SPECIAL mu=(0,1,0,0)',(0,0)),('SPECIAL mu=(0,1,0,1)',(0,1)),('SPECIAL mu=(0,1,1,0)',(1,0)),('SPECIAL mu=(0,1,1,1)',(1,1))):
    B=fam22(m3,m4); Bo=onb(B); le=level_err(Bo,ntest=60)
    T=T1(embed(Bo),rg,npts=140); U_,S,Vh=np.linalg.svd(T[:,4,:].T,full_matrices=False); r=int((S>1e-8*S[0]).sum())
    fo=[FO2(embed(Bo),np.random.default_rng(k),npts=140) for k in range(3)]
    print('%-26s dim %d level err %.0e srow %s scol %s e=%d PhiRk=%d dimE0=%d dimT1=%d dimOmega=%d FO2=%s'%(name,len(Bo),le,[len(rowpart(Bo,[i])) for i in range(4)],[len(colpart(Bo,[j])) for j in range(5)],int((defect(Bo)>1e-8).sum()),int((phirank(Bo)>1e-8).sum()),len(E0(Bo,rg)),len(T),r,fo))
    if 'SPECIAL' in name:
        Rr,_=rref(U_[:,:r].T.reshape(r,1,5)); print('      Omega:',np.array2string(Rr.reshape(r,5).real,precision=2).replace('\n',' '))
        np.save('dr22_special_%d%d.npy'%(m3,m4),Bo)
