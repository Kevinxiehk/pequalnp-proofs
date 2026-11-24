# sanity check of dim L <= dim T_1(L_r) - 1 on known 7-dim lifts: for every row r, dim T_1(L_r) >= 8, and y_r in T_1(L_r).
import sys, glob, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9')
import build7
from t1_c52 import T1, rank, cofs
for f in sorted(glob.glob('/home/kevxhk/work/L-gct-210/rows/clm_p4_d[456]_defect[123]_s*.npy'))[:6]:
    B,e=build7.build(np.load(f)); d=len(B); out=[]
    for r in range(5):
        A=np.array([[B[k][r,j] for k in range(d)] for j in range(5)]); u,s,vh=np.linalg.svd(A); rk=int((s>1e-7*s[0]).sum())
        C=vh[rk:].conj().T; Lr=np.tensordot(C.T,B,axes=1)                     # basis of L_r
        t=T1(Lr); out.append('r%d: dim L_r %d, T_1 %d'%(r,len(Lr),t[0]))
    print(f.split('/')[-1],'dim',d,' | '.join(out))
