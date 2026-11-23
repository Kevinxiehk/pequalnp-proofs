import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
import numpy as np, glob
from t import *
from a1 import embed, defect, pk, phirank
from a5 import onb
from a6 import T1, E0
from r5_FO2 import FO2
from show import rref
np.set_printoptions(precision=3,suppress=True,linewidth=200)
rg=np.random.default_rng(2)
for f in sorted(glob.glob('linespan_other_*.npy')):
    B=np.load(f); print('=====',f,'level err %.1e'%level_err(B),'rank',np.linalg.matrix_rank(B.reshape(6,20)))
    for m in B:
        nz=np.argwhere(np.abs(m)>1e-9)
        rows=sorted(set(nz[:,0])); cols=sorted(set(nz[:,1]))
        if len(rows)==1: print('  row',rows[0],np.array2string(m[rows[0]]/np.abs(m[rows[0]]).max(),precision=3))
        else: print('  col',cols[0],np.array2string(m[:,cols[0]]/np.abs(m[:,cols[0]]).max(),precision=3))
    Bo=onb(B); ds=defect(Bo,n=60); print('  defect sv',np.array2string(ds,precision=3))
    T=T1(embed(Bo),rg,npts=90); S=np.linalg.svd(T[:,4,:],compute_uv=False); print('  dim T1',len(T),'row-4 sv',np.array2string(S,precision=3),'dim E0',len(E0(Bo,rg)))
    U,S2,Vh=np.linalg.svd(T[:,4,:].T,full_matrices=False); r=int((S2>1e-7*S2[0]).sum()); 
    for v in U[:,:r].T: print('  Omega vec',np.array2string(v/v[np.argmax(abs(v))],precision=3))
    print('  FO2',FO2(embed(Bo),rg),'Phi sv',np.array2string(phirank(Bo),precision=2))
