import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/split'); sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
from exact7 import Zw, W, zero
import level
B=[]
M=zero()
for i in range(3): M[i][2]=W[(2*i)%3]; M[i][3]=-W[(2*i)%3]
B.append(M)
M=zero()
for i in range(3): M[i][2]=W[i]; M[i][3]=W[i]
B.append(M)
for j in range(4):
    M=zero(); M[3][j]=Zw(1); M[3][4]=Zw(-1); B.append(M)
M=zero()
for i in range(3): M[i][4]=Zw(1)
M[4][4]=Zw(-3); B.append(M)
print('ex3 exact check (k, #nonzero):',level.check_exact(B,5))
