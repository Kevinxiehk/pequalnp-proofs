# rank of a square matrix mod p (rows from the Singular file), and n - rank = length of A/(det)
import sys, numpy as np
P=int(sys.argv[2]); rows=[]
for line in open(sys.argv[1]):
    s=line.split()
    if s: rows.append([int(x)%P for x in s])
A=np.array(rows,dtype=np.int64); n=A.shape[0]; assert A.shape==(n,n)
r=0
for c in range(n):
    piv=None
    for i in range(r,n):
        if A[i,c]%P: piv=i; break
    if piv is None: continue
    A[[r,piv]]=A[[piv,r]]
    inv=pow(int(A[r,c]),P-2,P); A[r]=(A[r]*inv)%P
    col=A[:,c].copy(); col[r]=0
    nz=np.nonzero(col)[0]
    if len(nz): A[nz]=(A[nz]-np.outer(col[nz],A[r]))%P
    r+=1
print('n=%d rank=%d  length of A/(det) = %d'%(n,r,n-r))
