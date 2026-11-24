# invariants of the three non-split (5,2) spaces (candidates for the (S3-a) core L_e)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9')
import numpy as np, build7, itertools
from t1_c52 import rank
np.set_printoptions(precision=3,suppress=True,linewidth=160)
for f in ['c52_rand_242','c52_seedns_33','c52_seedns_39']:
    Z=np.load('/home/kevxhk/work/L-gct-210/rows/%s.npy'%f); d=len(Z); B,e=build7.build(Z); W=B[d:,4,:]
    def ker(cells): return d-rank(np.array([[Z[k][i,j] for k in range(d)] for (i,j) in cells])) if cells else d
    rowdim=[rank(Z[:,r,:]) for r in range(4)]
    lam={(r,q):ker([(r,j) for j in range(5)]+[(q,j) for j in range(5)]) for r in range(4) for q in range(r+1,4)}
    colz=[j for j in range(5) if np.abs(Z[:,:,j]).max()<1e-7]
    # columns where the defect-orthogonal plane W is constant: (C+C1)^perp = {w: s(w)=0, w const on S}
    print(f,'dim',d,'e',e,'row-projection dims',rowdim,'2-row kernels',lam,'zero columns',colz)
    print('   (C+C1)^perp basis (row e single-row plane):\n',W)
