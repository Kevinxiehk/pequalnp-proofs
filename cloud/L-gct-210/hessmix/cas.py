import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/hessmix')
from hk import *
from nya import Phi, nullsp, RowS, ColS
Bo=orth(examples()['L080']); Y=np.array([Phi(b).ravel() for b in Bo])
C=Y@ColS.T; R=Y@RowS.T
YA=nullsp(C.T)@Y            # rows: elements with C=0, R onto C^5_0
RA=YA@RowS.T                # their row sums (4x5)
# dual basis: rho_k = RA[k]; rho*_k with RA @ rhostar^T = I on C^5_0
Rs=np.linalg.pinv(RA).T     # (4x5): RA @ Rs.T = I
cA=sum(YA[k]*(Rs[k]@np.linalg.pinv(RA).T.T@YA if False else 0) for k in range(0)) if False else None
# Y_A element with row sums rho is linear in rho: A(rho) = rho @ pinv(RA) @ YA
Amap=np.linalg.pinv(RA)@YA*0+np.linalg.lstsq(RA,YA,rcond=None)[0]  # 5x25: rho -> A(rho)
E4=np.array([np.eye(5)[k]-np.eye(5)[4] for k in range(4)]); Gm=E4@E4.T; Di=np.linalg.inv(Gm)
cA=sum(Di[k,m]*(E4[k]@Amap)*(E4[m]@Amap) for k in range(4) for m in range(4))
print('L080: |<c_A, Y>| =',np.abs(Y@cA).max(),' <c_A,1> =',cA.sum(),' (20/9 =',20/9,')')
