import numpy as np, itertools
n=5; N=n*n
idx=[(i,j) for i in range(n) for j in range(n)]
Qf=np.array([[1.0 if (a[0]!=b[0] and a[1]!=b[1]) else 0 for b in idx] for a in idx])  # Hessian of P_2 (pair form)
def H(v):
    V=v.reshape(n,n); M=np.zeros((N,N))
    for x,(i,j) in enumerate(idx):
        for y,(k,l) in enumerate(idx):
            if i!=k and j!=l:
                rows=[m for m in range(n) if m not in (i,k)]; cols=[p for p in range(n) if p not in (j,l)]
                M[x,y]=V[np.ix_(rows,cols)].sum()
    return M
# basis of sum-zero matrices (P_1=0): 24-dim
B=np.linalg.svd(np.ones((1,N)))[2][1:].T   # N x 24 orthonormal, orthogonal to ones
Q=B.T@Qf@B
print('Q rank',np.linalg.matrix_rank(Q))
rng=np.random.default_rng(0)
def A(c): return np.linalg.solve(Q,B.T@H(B@c)@B)
c1=rng.normal(size=24); c2=rng.normal(size=24)
A1=A(c1);A2=A(c2)
print('commutator norm',np.linalg.norm(A1@A2-A2@A1),' vs ',np.linalg.norm(A1@A2))
# DC subspace check
C=[]
for i in range(n):
    r=np.zeros((n,n)); r[i,:]=1; C.append(r.ravel())
    c=np.zeros((n,n)); c[:,i]=1; C.append(c.ravel())
D=np.linalg.svd(np.array(C))[2][9:].T  # 25x16 DC basis
QD=D.T@Qf@D; print('DC: Q prop to identity?',np.allclose(QD,QD[0,0]*np.eye(16)) , QD[0,0])
