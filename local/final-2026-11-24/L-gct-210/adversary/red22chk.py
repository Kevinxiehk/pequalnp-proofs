import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
import numpy as np
from level import Pk
rng=np.random.default_rng(3); err=0
for _ in range(5):
    t=np.zeros((5,5),complex); M=rng.normal(size=(5,5))+1j*rng.normal(size=(5,5))
    t[:2,:]=M[:2,:]; t[:,:2]=M[:,:2]
    Z=t[:2,:2]; X=t[:2,2:]; Y=t[2:,:2]
    s1,s2=X.sum(1); c1,c2=Y.sum(0)
    q=s1*s2-X[0]@X[1]; qY=c1*c2-Y[:,0]@Y[:,1]
    R1,R2=Z.sum(1); K1,K2=Z.sum(0); pZ=Z[0,0]*Z[1,1]+Z[0,1]*Z[1,0]
    E1=s1+s2+Z.sum()+c1+c2
    E2=q+qY+(s1+s2)*(c1+c2)+s1*R2+s2*R1+pZ+c1*K2+c2*K1
    E3=c1*(s1*Z[1,1]+s2*Z[0,1])+c2*(s1*Z[1,0]+s2*Z[0,0])+(s1+s2)*qY+(c1+c2)*q
    E4=q*qY
    P=Pk(t)[0]
    err=max(err,abs(P[1]-E1),abs(P[2]-E2),abs(P[3]-E3),abs(P[4]-E4),abs(P[5]))
print('max err reduction 2+2 cover:',err)
# ranks
def symm(coef,n):
    M=np.zeros((n,n))
    for (a,b),v in coef.items():
        if a==b: M[a,a]+=v
        else: M[a,b]+=v/2; M[b,a]+=v/2
    return M
# vars Z11 Z12 Z21 Z22 s1 s2 : G_X (c=0 branch)
G=symm({(0,3):1,(1,2):1,(4,2):1,(4,3):1,(5,0):1,(5,1):1,(4,5):2/3},6)
print('rank G_X (c=0 branch) on C^6:',np.linalg.matrix_rank(G))
