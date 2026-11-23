# WRITTEN AT HANDOVER (20:35), NOT RUN.  Numerical invariants of random members of pattern (2,1,1|2), incidence case (ii):
#   M = C e_0 (5e_0 - 1)^T + C e_0 (0,a)^T + C e_1 (0,b)^T + C e_2 (0,c)^T + {x e_0^T : x_0 = 0, sum x = 0},
#   a, b, c in C^4 (columns 1..4) sum-zero, pairwise orthogonal, sum_j a_j b_j c_j = 0.
# Prints (level error, e, dim E_0, dim T_1, dim Omega, FO2) and a basis of Omega.  Expected runtime 10 s.  Run from reg2/: python3 -I dr211b_num.py
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
import numpy as np
from t import *
from a1 import embed, defect
from a5 import onb
from a6 import T1, E0
from r5_FO2 import FO2
from show import rref
np.set_printoptions(precision=3,suppress=True,linewidth=200)
def member(a,b,c):
    B=np.zeros((6,4,5),complex)
    B[0,0]=[4,-1,-1,-1,-1]; B[1,0,1:]=a; B[2,1,1:]=b; B[3,2,1:]=c
    B[4,1,0]=1; B[4,2,0]=-1; B[5,2,0]=1; B[5,3,0]=-1
    return B
rg=np.random.default_rng(5)
for trial in range(6):
    a=rg.normal(size=4)+1j*rg.normal(size=4); a-=a.mean()
    A=np.array([np.ones(4),a]); P=null(A); p,q=P[0],P[1]; G=np.array([[p@p,p@q],[q@p,q@q]])
    def bc(th):
        c1=np.array([1,th]); b=c1[0]*p+c1[1]*q; g=G@c1; c3=np.array([-g[1],g[0]]); return b,c3[0]*p+c3[1]*q
    f=lambda th:(a*bc(th)[0]*bc(th)[1]).sum()
    ths=np.array([0,1,-1]); co=np.polyfit(ths,[f(t) for t in ths],2); th=np.roots(co)[trial%2]
    b,c=bc(th); Bo=onb(member(a,b,c))
    T=T1(embed(Bo),rg,npts=140); U_,S,Vh=np.linalg.svd(T[:,4,:].T,full_matrices=False); r=int((S>1e-8*S[0]).sum())
    print('member %d: dim %d level err %.0e e=%d dimE0=%d dimT1=%d dimOmega=%d FO2=%s'%(trial,len(Bo),level_err(Bo,ntest=50),int((defect(Bo)>1e-8).sum()),len(E0(Bo,rg)),len(T),r,FO2(embed(Bo),rg,npts=140)))
    Rr,_=rref(U_[:,:r].T.reshape(r,1,5)); print('   Omega (rref):',np.array2string(Rr.reshape(r,5),precision=2).replace('\n',' '))
