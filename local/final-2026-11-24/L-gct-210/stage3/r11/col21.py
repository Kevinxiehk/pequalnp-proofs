# column-side invariants of the (2,1,0,0)/(2,2,2,2) examples: single-column dims (elements supported in one column), column projection
# ranks, and the dimension of {elements supported in column c} with zero sum (partial free column parts), per column.
import sys, glob, itertools, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9'); from t1_c52 import rank, single_rows
fs=sorted(glob.glob('/home/kevxhk/work/L-gct-210/stage3/r9/pr2_sol_*.npy'))+sorted(glob.glob('/home/kevxhk/work/L-gct-210/stage3/r10/pr2split_sol_*.npy'))
for f in fs:
    Z=np.load(f); d=len(Z)
    def ker(cells): return d-rank(np.array([[Z[k][i,j] for k in range(d)] for (i,j) in cells]))
    sc=[ker([(i,j) for i in range(4) for j in range(5) if j!=c]) for c in range(5)]          # single-column parts
    cp=[rank(Z[:,:,c]) for c in range(5)]                                                    # column projection ranks
    eq=[]                                                                                     # pairs of columns equal on the whole space
    for a,b in itertools.combinations(range(5),2):
        if np.abs(Z[:,:,a]-Z[:,:,b]).max()<1e-7: eq.append((a,b))
    print('%-22s single-row %s  single-col %s  col-proj ranks %s  identical column pairs %s'%(f.split('/')[-1],single_rows(Z),sc,cp,eq))
