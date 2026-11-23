# column-centred kernel K = ker(column sums) of extremal spaces: dim, defect of K, row-sum rank on K, single-row/column content
import sys,glob; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np
from clm import *
from ext_chk import lines
def kernel_colsum(Z,tol=1e-5):
    d=Z.shape[0]; c=Z.sum(1)                       # (d,5)
    u,s,vh=np.linalg.svd(c.T,full_matrices=True); r=int((s>tol).sum())
    K=np.einsum('ak,kij->aij',vh[r:].conj(),Z); return r,K
if __name__=='__main__':
    tab={}
    for pat in sys.argv[1:]:
        for f in sorted(glob.glob(pat)):
            Z=np.load(f); d=Z.shape[0]; lev,row,col,e=lines(Z)
            if d!=e+3: continue
            r,K=kernel_colsum(Z)
            if len(K)==0: key=(d,e,r,0,0,0)
            else:
                sv=defect_dim(K); eK=int((sv>1e-4).sum()); rs=np.linalg.svd(K.sum(2),compute_uv=False); qs=int((rs>1e-5).sum())
                key=(d,e,r,K.shape[0],eK,qs)
            tab[key]=tab.get(key,0)+1
    print('(d,e, rank colsum, dim K, e(K), rowsum rank on K): count')
    for k in sorted(tab): print('  ',k,':',tab[k])
