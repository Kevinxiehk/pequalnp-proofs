import sys; sys.path.insert(0,'.')
import numpy as np
from core import u, ub, chi
Z=np.load('pol3_s1.npy')  # 15 x 5, basis of 3x5 matrices
Q,_=np.linalg.qr(Z)
one=np.array([1,1,1.])
uu=u[:3]; uub=ub[:3]
# decompose each basis matrix X (3x5) = 1 o^T + u p^T + ub q^T ; coefficients via inverse of [1,u,ub]/3
Minv=np.array([one,uu.conj(),uub.conj()])/3
O=[];P=[];Qq=[]
for k in range(5):
    X=Q[:,k].reshape(3,5); C=Minv@X; O.append(C[0]);P.append(C[1]);Qq.append(C[2])
O=np.array(O).T;P=np.array(P).T;Qq=np.array(Qq).T
for name,M in [('o',O),('p',P),('q',Qq)]:
    s=np.linalg.svd(M,compute_uv=False); print(name,'component singular values',np.round(s,5))
F=np.array([chi(a) for a in range(5)]).conj()/5   # Fourier coefficients
for name,M in [('o',O),('p',P),('q',Qq)]:
    print(name,'Fourier weight norms',np.round(np.linalg.norm(F@M,axis=1),4))
# Gram of the quadric Q(o,p,q)= p.q - sum p sum q - sum o^2 on the space
def bil(i,j):
    return 0.5*(P[:,i]@Qq[:,j]+P[:,j]@Qq[:,i]) -0.5*(P[:,i].sum()*Qq[:,j].sum()+P[:,j].sum()*Qq[:,i].sum()) - O[:,i]@O[:,j]
G=np.array([[bil(i,j) for j in range(5)] for i in range(5)]); print('|Gram Q| max',np.abs(G).max())
