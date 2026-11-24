# (S3-a) needs L_e = 5-dim 4x5 level space with ALL four row projections of dim 2 and no single-row element. Census of stored 5-dim 4x5 spaces.
import sys, glob; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9')
import numpy as np, build7
from t1_c52 import rank, single_rows
cnt={}
for f in sorted(glob.glob('/home/kevxhk/work/L-gct-210/rows/*.npy')):
    try: Z=np.load(f)
    except Exception: continue
    if Z.ndim!=3 or Z.shape[1:]!=(4,5) or len(Z)!=5: continue
    if build7.check(np.concatenate([np.concatenate([Z,np.zeros((5,1,5))],axis=1)]),n=3)>1e-6: continue
    rd=tuple(sorted(rank(Z[:,r,:]) for r in range(4))); u=tuple(sorted(single_rows(Z),reverse=True))
    k=(rd,u); cnt.setdefault(k,[]).append(f.split('/')[-1])
for k,v in sorted(cnt.items()): print('row-projection dims',k[0],' single-row dims',k[1],': %d spaces, e.g. %s'%(len(v),v[:3]))
