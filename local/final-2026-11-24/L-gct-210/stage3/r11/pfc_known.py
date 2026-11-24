# Do known 7-dim level spaces contain a free column (or row) on four entries?  For each column j: dim of the single-column part
# {v : v e_j^T in L} and whether it contains {v : v_i = 0, sum v = 0} for some i (then dim >= 3).
import sys, glob, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); import build7
def rank(A,tol=1e-7):
    s=np.linalg.svd(np.atleast_2d(A),compute_uv=False); return int((s>tol*max(1,s[0])).sum())
def single_parts(B,transpose=False):
    B=np.transpose(B,(0,2,1)) if transpose else B; d=len(B); out=[]
    for j in range(5):   # elements supported in column j: kernel of the other columns
        A=np.array([[B[k][i,c] for k in range(d)] for c in range(5) if c!=j for i in range(5)])
        out.append(d-rank(A))
    return out
for f in sorted(glob.glob('/home/kevxhk/work/L-gct-210/rows/clm_p4_d[3456]_defect[0123]_s*.npy')):
    B,e=build7.build(np.load(f))
    if len(B)!=7: continue
    print('%-28s single-column dims %s   single-row dims %s'%(f.split('/')[-1],single_parts(B),single_parts(B,True)))
