# Census of the known level spaces: a_r, b_c, zero patterns of the row/column annihilators (when unique), single-row/column dims.
import sys, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import core
from pairlib import nullspace, rank
np.set_printoptions(precision=3,suppress=True,linewidth=200)
for name,sp in core.SP.items():
    B=np.array([np.array(m,dtype=complex) for m in sp()]); d=len(B)
    a=[5-rank(B[:,r,:]) for r in range(5)]; b=[5-rank(B[:,:,c]) for c in range(5)]
    def single(axis,i):
        # elements supported in row i (axis=1) or column i (axis=2)
        M=B.copy()
        if axis==1: M=np.delete(M,i,axis=1)
        else: M=np.delete(M,i,axis=2)
        return d-rank(M.reshape(d,-1))
    z=[single(1,r) for r in range(5)]; zc=[single(2,c) for c in range(5)]
    lam=[[d-rank(B[:,[r,s],:].reshape(d,-1)) for s in range(5)] for r in range(5)]
    print(name,'dim',d,' a=',a,' b=',b,' z_row=',z,' z_col=',zc)
    for r in range(5):
        if a[r]==1:
            k=nullspace(B[:,r,:])[:,0]; k=k/k[np.argmax(abs(k))]
            print('   row',r,'kappa zero set:',[j for j in range(5) if abs(k[j])<1e-8])
    for c in range(5):
        if b[c]==1:
            k=nullspace(B[:,:,c])[:,0]; k=k/k[np.argmax(abs(k))]
            print('   col',c,'kappa\' zero set:',[i for i in range(5) if abs(k[i])<1e-8])
