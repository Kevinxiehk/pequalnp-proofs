# Round 9 probe for z_e = 1: L contains M6 = L_e (+) C e_e w^T (L_e a 5-dim 4x5 level space, w in (C(L_e)+C1)^perp), and L lies in T_1(M6).
# Census of dim T_1(M6) for (5,2) spaces (w generic in the 2-dim (C+C1)^perp) and for (5,3) spaces (random 5-dim subspaces of (6,3) spaces).
import sys, glob, itertools
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9')
import numpy as np, build7
from t1_c52 import T1, single_rows, rank
rg=np.random.default_rng(9); out={}
def lift_part(Z,k=None):
    B,e=build7.build(Z); d=len(Z); S=B[d:]                      # single-row part (C+C1)^perp in row e
    if k is not None and len(S)>k: C=rg.normal(size=(k,len(S)))+1j*rg.normal(size=(k,len(S))); S=np.einsum('ik,kab->iab',C,S)
    return np.concatenate([B[:d],S]),e
for f in sorted(glob.glob('/home/kevxhk/work/L-gct-210/rows/c52_*.npy')+glob.glob('/home/kevxhk/work/L-gct-210/rows/clm_p4_d5_defect2_*.npy')):
    Z=np.load(f); M6,e=lift_part(Z,1); t=T1(M6); key=('(5,2)+1 single-row vector','nosplit' if sum(single_rows(Z))==0 else 'split',t[0]); out[key]=out.get(key,0)+1
for f in sorted(glob.glob('/home/kevxhk/work/L-gct-210/rows/clm_p4_d6_defect3_*.npy')):
    Z6=np.load(f)
    for rep in range(3):
        C=rg.normal(size=(5,6))+1j*rg.normal(size=(5,6)); Z=np.einsum('ik,kab->iab',C,Z6)
        M,e=lift_part(Z); t=T1(M); key=('(5,%d) lift (subspace of (6,3))'%e,'dim lift %d'%len(M),t[0]); out[key]=out.get(key,0)+1
        print(f.split('/')[-1],'rep',rep,'defect',e,'dim lift',len(M),'level err %.1e'%build7.check(M),'dim T_1',t[0],'gap %.0e/%.0e'%(t[1],t[2]),flush=True)
for k,v in sorted(out.items()): print(k,v)
