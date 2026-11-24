# Round 11, target 3: the (1,1,1|1,1,1) space found by the incidence split (S = 000001011; unique up to the S_3 x S_3 incidence symmetry,
# and the 36 nonempty incidence classes form one orbit): rational basis, numerical invariants.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from nc_num import report
from pieces import sub_supported
B=np.zeros((6,4,5))
B[0][0]=[0,0,0,1,-1]; B[1][1]=[0,0,-2,1,1]; B[2][2]=[0,-3,1,1,1]
B[3][:,0]=[1,1,-3,1]; B[4][:,1]=[1,-2,0,1]; B[5][:,2]=[1,0,0,-1]
np.save('/home/kevxhk/work/L-gct-210/reg2/p111/M111.npy',B)
report('M111 (1,1,1|1,1,1)',B)
a=[len(sub_supported(B,np.eye(4,dtype=bool)[i][:,None].repeat(5,1))) for i in range(4)]
b=[len(sub_supported(B,np.eye(5,dtype=bool)[c][None,:].repeat(4,0))) for c in range(5)]
print('single-row dims',a,' single-column dims',b,' rank',np.linalg.matrix_rank(B.reshape(6,-1)))
