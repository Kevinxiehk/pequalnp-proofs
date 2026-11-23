import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
import numpy as np, glob
from t import *
from a1 import Phi, phirank, defect, embed
from r5_FO2 import FO2
from show import rref
# limit spaces: rref with rounding at 1e-5, then report level error and invariants of the rounded space
def rref_tol(B,tol):
    d=len(B); sh=B.shape[1:]; A=B.reshape(d,-1).astype(complex).copy(); r=0
    for _ in range(d):
        sub=np.abs(A[r:]); i,j=np.unravel_index(np.argmax(sub),sub.shape); i+=r
        if abs(A[i,j])<1e-9: break
        A[[r,i]]=A[[i,r]]; A[r]/=A[r,j]
        for k in range(d):
            if k!=r: A[k]-=A[k,j]*A[r]
        r+=1
    A[np.abs(A)<tol]=0
    return A[:r].reshape((r,)+sh)
def onb(B):
    d=len(B); sh=B.shape[1:]; u,s,vh=np.linalg.svd(B.reshape(d,-1),full_matrices=False); r=int((s>1e-8*s[0]).sum()); return vh[:r].reshape((r,)+sh)
if __name__=='__main__':
    rg=np.random.default_rng(3)
    fs=sorted(glob.glob('../rows/rc45.npy')+glob.glob('../rows/clm_p4_d6_*.npy')+glob.glob('../rows/nc_d6_*.npy')+glob.glob('../rows/seed_d6_*.npy'))
    for f in fs:
        B0=np.load(f); R=rref_tol(onb(B0),1e-5); B=onb(R)
        le=level_err(B)
        rr=[rank(B[:,i,:],1e-6) for i in range(4)]; cc=[rank(B[:,:,j],1e-6) for j in range(5)]
        sr=[len(rowpart(B,[i])) for i in range(4)]; sc=[len(colpart(B,[j])) for j in range(5)]
        ps=phirank(B); ds=defect(B); pr=int((ps>1e-6).sum()); dr=int((ds>1e-6).sum())
        n,rho,bd=FO2(embed(B),rg)
        print('%-28s limit: lev %.0e rowrk %s colrk %s srow %s scol %s Phi-rk %d defect %d T1 %d rk %d FO2 %d'%(f.split('/')[-1],le,rr,cc,sr,sc,pr,dr,n,rho,bd))
