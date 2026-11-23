import sys; sys.path.insert(0,'.')
from exact7 import Zw, W, zero
import level
B=[]
for col in (0,1):
    M=zero()
    for i in range(3): M[i][col]=W[i]
    B.append(M)
for j in range(4):
    M=zero(); M[3][j]=Zw(1); M[3][4]=Zw(-1); B.append(M)
M=zero()
for i in range(3): M[i][4]=Zw(1)
M[4][4]=Zw(-3); B.append(M)
print('(6,1) space:',level.check_exact(B,5))
