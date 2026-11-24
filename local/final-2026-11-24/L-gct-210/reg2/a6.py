import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, glob
from t import *
from a1 import Phi, phirank, defect, embed
from r5_FO2 import FO2, cof55
from a5 import rref_tol, onb
def T1(Mb,rg,npts=80,tol=1e-8):
    Mb=np.asarray(Mb,complex).reshape(len(Mb),25); d=len(Mb); rows=[]
    for _ in range(npts):
        c=rg.normal(size=d)+1j*rg.normal(size=d); rows.append(cof55(np.ones((5,5))+(c@Mb).reshape(5,5)))
    u,s,vh=np.linalg.svd(np.array(rows)); r=int((s>tol*s[0]).sum()); return vh[r:].conj().reshape(-1,5,5)
def E0(B,rg,npts=80,tol=1e-8):
    # 4x5 first-order extension space: X' with D_X' F(J'+Y)=0 : gradient of 4x5 level poly = cofactor rows 0..3 of the 5x5 matrix with row 4 = ones
    Mb=embed(B).reshape(len(B),25); d=len(B); rows=[]
    for _ in range(npts):
        c=rg.normal(size=d)+1j*rg.normal(size=d); rows.append(cof55(np.ones((5,5))+(c@Mb).reshape(5,5))[:20])
    u,s,vh=np.linalg.svd(np.array(rows)); r=int((s>tol*s[0]).sum()); return vh[r:].conj().reshape(-1,4,5)
if __name__=='__main__':
    rg=np.random.default_rng(3)
    fs=sorted(glob.glob('../rows/rc45.npy')+glob.glob('../rows/clm_p4_d6_*.npy')+glob.glob('../rows/nc_d6_*.npy')+glob.glob('../rows/seed_d6_*.npy'))
    for f in fs:
        B0=np.load(f); R=rref_tol(onb(B0),1e-5); B=onb(R)
        if level_err(B)>1e-9: B=onb(B0); tag='raw'
        else: tag='lim'
        T=T1(embed(B),rg); E=E0(B,rg)
        ps=phirank(B); pr=int((ps>1e-6).sum()); ds=defect(B); e=int((ds>1e-6).sum())
        # Phi span basis
        rng=np.random.default_rng(1); V=np.array([Phi(np.einsum('k,kab->ab',rng.normal(size=len(B))+1j*rng.normal(size=len(B)),B)) for _ in range(30)])
        u,s,vh=np.linalg.svd(V); K=vh[:pr]            # rows span Phi(M) (conj convention irrelevant for bilinear test below: use V directly)
        rho=T[:,4,:]                                   # row-r parts of T_1
        rr=rank(rho,1e-7) if len(T) else 0
        # T_1 cap {rho' perp Phi(M)}
        if pr>0:
            A=(rho@V[:pr+2].T).T   # conditions <rho',Phi_s>=0
            C=null(A,1e-7); T2=np.einsum('kc,cab->kab',C,T)
        else: T2=T
        rr2=rank(T2[:,4,:],1e-7) if len(T2) else 0
        print('%-26s %s e=%d PhiRk=%d dimE0=%d dimT1=%d g=%d rowproj(T1)=%d | T1&PhiPerp: dim %d rowproj %d'%(f.split('/')[-1],tag,e,pr,len(E),len(T),len(T)-len(E)-(4-e),rr,len(T2),rr2))
