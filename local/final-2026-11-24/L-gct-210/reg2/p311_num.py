# pattern (3,1|1,1) with ISOTROPIC m (the cases not covered by SP8; hand reduction NOTES-reg2 9.7):
#   M = e_0 (x) {1,m}^perp (+) C e_1 m^T (+) C x e_c^T (+) C x' e_c'^T,  x, x' in {x_0 = 0, sum = 0} (rows 1..3), <x,x'> = 0.
#   (A) m_c = m_c' = 0: m = (1, w, w^2) on the three other columns;  (B) m_c = 0, x' = e_2 - e_3 (x'_1 = 0), x in {x_0=0} perp x'.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from t import *
from a1 import embed, defect
from a5 import onb
from a6 import T1, E0
from r5_FO2 import FO2
def fam(m,c,x,cp,xp):
    m=np.array(m,complex); K=null(np.array([np.ones(5),m])); B=np.zeros((6,4,5),complex)
    for k in range(3): B[k,0]=K[k]
    B[3,1]=m; B[4,:,c]=x; B[5,:,cp]=xp
    return B
w=np.exp(2j*np.pi/3); rg=np.random.default_rng(0)
def iso4(t):
    s=-1-t; q=1+t*t; p=(s*s+q)/2; disc=np.sqrt(s*s-4*p+0j); return [1,t,(s+disc)/2,(s-disc)/2,0]
cases=[]
# (A): m on columns 0,1,2; c = 3, c' = 4; x, x' orthogonal in {x_0 = 0, sum = 0}
for th in (0.3,1.1+0.4j,0.0):
    x=np.array([0,1,-1,0],complex)*np.cos(th)+np.array([0,1,1,-2],complex)/np.sqrt(3)*np.sin(th)
    xp=np.array([0,1,-1,0],complex)*(-np.sin(th))+np.array([0,1,1,-2],complex)/np.sqrt(3)*np.cos(th)
    cases.append(('A th=%s'%th,[1,w,w*w,0,0],3,x,4,xp))
# (B): m isotropic with m_4 = 0 (column c = 4 carries x), x' = e_2 - e_3 in column c' (any column), x perp x' in {x_0 = 0}
for t in (0.3,2+1j):
    for cp in (0,3):
        cases.append(('B t=%s cp=%d'%(t,cp),iso4(t),4,np.array([0,2,-1,-1],complex),cp,np.array([0,0,1,-1],complex)))
cases.append(('B m=(1,i,-1,-i,0) cp=0',[1,1j,-1,-1j,0],4,np.array([0,2,-1,-1],complex),0,np.array([0,0,1,-1],complex)))
for (k,m,c,x,cp,xp) in cases:
    Bo=onb(fam(m,c,x,cp,xp)); le=level_err(Bo,ntest=30)
    if len(Bo)<6 or le>1e-8: print('%-26s dim %d level err %.1e  (not a 6-dim level space)'%(k,len(Bo),le)); continue
    T=T1(embed(Bo),rg,npts=160); U_,S,Vh=np.linalg.svd(T[:,4,:].T,full_matrices=False); r=int((S>1e-8*S[0]).sum())
    fo=FO2(embed(Bo),np.random.default_rng(1),npts=160)
    print('%-26s lev %.0e e=%d dimE0=%d dimT1=%d dimOmega=%d FO2=%s'%(k,le,int((defect(Bo)>1e-8).sum()),len(E0(Bo,rg,npts=160)),len(T),r,fo),flush=True)
