import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
import numpy as np, glob
from t import *
from a1 import embed, defect, phirank
from a5 import onb
from a6 import T1, E0
from r5_FO2 import FO2
from show import rref
np.set_printoptions(precision=3,suppress=True,linewidth=200)
rg=np.random.default_rng(2)
for f in sys.argv[1:]:
    B=np.load(f); Bo=onb(B)
    print('=====',f,'level err %.1e (200 pts)'%level_err(Bo,ntest=200,seed=5))
    def part(mask):
        A=Bo.reshape(6,-1)[:,~mask.ravel()].T; return np.linalg.svd(A,compute_uv=False)
    for i in range(4):
        mk=np.zeros((4,5),bool); mk[i]=True; print('  row',i,'restriction sv',np.array2string(part(mk),precision=2))
    print('  defect sv',np.array2string(defect(Bo,n=60),precision=3),' Phi sv',np.array2string(phirank(Bo),precision=2))
    T=T1(embed(Bo),rg,npts=100); S=np.linalg.svd(T[:,4,:],compute_uv=False)
    print('  dim T1',len(T),'row-4 sv',np.array2string(S,precision=3),'dim E0',len(E0(Bo,rg)),'FO2',FO2(embed(Bo),rg))
    U,S2,Vh=np.linalg.svd(T[:,4,:].T,full_matrices=False); r=int((S2>1e-7*S2[0]).sum())
    R,_=rref(U[:,:r].T.reshape(r,1,5)); print('  Omega (rref):'); print(R.reshape(r,5))
    # the single-row part of row 3: U ; its annihilator
    mk=np.zeros((4,5),bool); mk[3]=True; SR=sub_supported(Bo,mk); Um=SR[:,3,:]
    u,s,vh=np.linalg.svd(Um); print('  U = single-row part of row 3: dim',len(SR),' annihilator (rows):'); print(vh[len(SR):].conj() if False else np.round(np.linalg.svd(Um)[2][len(SR):],3))
