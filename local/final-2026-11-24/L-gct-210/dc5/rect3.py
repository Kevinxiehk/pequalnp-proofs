import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/dc5'); sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
import numpy as np
from blocksrch import run
rows=[int(c) for c in sys.argv[1]]
A=np.zeros((5*len(rows),5,5))
for a,i in enumerate(rows):
    for j in range(5): A[a*5+j,i,j]=1
d=int(sys.argv[2]); f,T,ns=run(A,d,[1,2,3,4,5],int(sys.argv[3]),int(sys.argv[4]),float(sys.argv[5]))
print('rows',rows,'(all matrices on these rows) d',d,'best res %.2e'%f,'starts',ns); np.save(f'rect_{sys.argv[1]}_d{d}.npy',T)
