import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
import numpy as np, glob
from t import *
from a1 import embed, defect
from a5 import rref_tol, onb
from a6 import T1, E0
np.set_printoptions(precision=3,suppress=True,linewidth=200)
def Omega(B,rg,tol=1e-8):
    T=T1(embed(B),rg,tol=tol); rho=T[:,4,:]
    U,S,Vh=np.linalg.svd(rho.T,full_matrices=False); r=int((S>1e-6*S[0]).sum()); return U[:,:r].T, len(T)
def alg_closure_dim(Om):
    # dim of span of Om and entrywise products
    P=[a*b for a in Om for b in Om]; A=np.array(list(Om)+P); return rank(A,1e-6)
if __name__=='__main__':
    rg=np.random.default_rng(3)
    fs=sorted(glob.glob('../rows/clm_p4_d3_*.npy')+glob.glob('../rows/clm_p4_d4_*.npy')+glob.glob('../rows/clm_p4_d5_*.npy'))
    for f in fs:
        B=onb(np.load(f)); le=level_err(B)
        Om,nT=Omega(B,rg,tol=1e-7); e=int((defect(B)>1e-6).sum())
        print('%-32s dim %d lev %.0e e=%d dimT1=%d dimOmega=%d algclosure=%d'%(f.split('/')[-1],len(B),le,e,nT,len(Om),alg_closure_dim(Om)))
    # random subspaces of the 6-dim examples
    for f in ['../rows/rc45.npy','../rows/nc_d6_k1_s23.npy','../rows/nc_d6_k1_s4.npy','../rows/seed_d6_e3_t4.npy','../rows/nc_d6_k1_s20.npy']:
        B0=np.load(f); B=onb(rref_tol(onb(B0),1e-5))
        for d in (5,4,3):
            for trial in range(2):
                C=rg.normal(size=(d,6))+1j*rg.normal(size=(d,6)); Bs=onb(np.einsum('kc,cab->kab',C,B))
                Om,nT=Omega(Bs,rg); e=int((defect(Bs)>1e-6).sum())
                print('%-24s sub dim %d e=%d dimT1=%d dimOmega=%d algclosure=%d'%(f.split('/')[-1],d,e,nT,len(Om),alg_closure_dim(Om)))
