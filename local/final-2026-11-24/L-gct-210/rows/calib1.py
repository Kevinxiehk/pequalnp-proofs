import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np
from rect import *
# planted: F_3 + E_j in 3x5
def planted35(j=1):
    B=[]
    for k in range(4):
        M=np.zeros((3,5),complex); M[2,k]=1; M[2,4]=-1; B.append(M)
    M=np.zeros((3,5),complex); M[0,j]=1; M[1,j]=-1; B.append(M)
    return np.array(B)
Z=planted35(); print('planted 3x5 fresh',fresh(Z,0),describe(Z))
# embed in 4x5 with zero row: degenerate
Z4=np.zeros((5,4,5),complex); Z4[:,:3,:]=Z; print('4x5 padded: fresh(deg)',fresh(Z4,1))
# n=4 d=5 solution padded with zero column
S=np.load('/home/kevxhk/work/L-gct-086/smallcases/sol_n4_d5_full_s0.npy'); print('sol_n4_d5 shape',S.shape)
S=np.asarray(S,complex).reshape(-1,4,4); Z5=np.zeros((len(S),4,5),complex); Z5[:,:,:4]=S
print('sol_n4_d5 padded: fresh(level,deg)',fresh(Z5,0),fresh(Z5,1),describe(Z5))
