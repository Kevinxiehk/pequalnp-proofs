import sys; sys.path.insert(0,'.')
from level import *
rng=np.random.default_rng(2)
for n in range(2,7):
    Ti=rng.integers(-3,4,size=(n,n))
    P=Pk(Ti.astype(float))[0]; Pe=Pk_exact(Ti.tolist())
    # also perm(J+T) = sum (n-k)! P_k
    print(n, np.max(np.abs(P-np.array(Pe,dtype=float))))
    T=rng.normal(size=(1,n,n))+1j*rng.normal(size=(1,n,n))
    P,G=Pk_grad(T); E=rng.normal(size=(n,n)); h=1e-6
    fd=(Pk(T+h*E)-Pk(T-h*E))/(2*h)
    print('  grad err',np.max(np.abs(fd[0]-np.einsum('kab,ab->k',G[0],E))))
for n in range(3,7):
    B=construction_2n3(n)
    print('2n-3 exact n=',n,'dim',len(B),'rank',np.linalg.matrix_rank(np.array(B,dtype=float).reshape(len(B),-1)),check_exact(B,n))
