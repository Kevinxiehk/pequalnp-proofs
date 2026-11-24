import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/dc5'); sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
import numpy as np
from blocksrch import ambient, run
from fullext import extdim_full
import tangent as TG
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/dc5')
from hess import hdims
A=ambient([0,1,2])
for seed in range(6):
    f,T,ns=run(A,4,[2,3],15,100+seed,25)
    if f>1e-9: print('seed',seed,'no sol',f); continue
    T=T/np.abs(T).max()
    print('seed',seed,'res %.1e'%f,'full ext',extdim_full(T),'hess',hdims(T,[3,4,5])[1],'ranks',sorted(np.linalg.matrix_rank(b,1e-8) for b in T))
