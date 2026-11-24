import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/adversary'); sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
import numpy as np
from symm import *
from level import construction_2n3
L0=np.array(construction_2n3(5),float).reshape(7,25)
N,V=eigenspaces(perm_entries(G['g44']))
for e,Ve in enumerate(V):
    # dim of L0 ∩ Ve
    M=np.vstack([L0,Ve]); r=np.linalg.matrix_rank(M,1e-9); print(e, 7+Ve.shape[0]-r)
