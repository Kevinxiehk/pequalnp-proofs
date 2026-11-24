# EXACT rational space  M* = e_3 (x) {w : sum w = 0, w_1 = w_2}  (+)  C x e_0^T  (+)  C y e_3^T  (+)  C e_2 (e_1 - e_2)^T,
#   x = (1,-1,0), y = (1,1,-2) on rows 0,1,2  (x.y = 0, sum x = sum y = 0).   No full free row (row 3 carries only a 3-dim part).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from fractions import Fraction as Fr
import numpy as np
from exact_T1 import certificate, nullspace, cof
def E(cells):
    m=[[Fr(0)]*5 for _ in range(4)]
    for (i,j,v) in cells: m[i][j]=Fr(v)
    return m
B=[E([(3,0,2),(3,1,-1),(3,2,-1)]),E([(3,3,2),(3,1,-1),(3,2,-1)]),E([(3,4,2),(3,1,-1),(3,2,-1)]),
   E([(0,0,1),(1,0,-1)]),E([(0,3,1),(1,3,1),(2,3,-2)]),E([(2,1,1),(2,2,-1)])]
if __name__=='__main__':
    certificate(B,'M* (deletable row 3 with U = {sum w = 0, w_1 = w_2}, equal-column extension)',npts=320)
    Bn=np.array([[[float(v) for v in row] for row in m] for m in B],dtype=complex); np.save('Mstar2.npy',Bn)
    from t import *
    from a1 import embed, defect, phirank
    from a5 import onb
    from a6 import T1, E0
    from r5_FO2 import FO2
    rg=np.random.default_rng(0); Bo=onb(Bn)
    T=T1(embed(Bo),rg,npts=120); S=np.linalg.svd(T[:,4,:],compute_uv=False)
    print('numerical: level err %.1e, e = %d, dim T1 = %d, dim E0 = %d, dim Omega = %d, FO2 (n, rank, bound) = %s, Phi sv %s'%(level_err(Bo,ntest=100),int((defect(Bo)>1e-8).sum()),len(T),len(E0(Bo,rg)),int((S>1e-8).sum()),FO2(embed(Bo),rg),np.array2string(phirank(Bo),precision=2)))
    for k in range(3): print('   FO2 again',FO2(embed(Bo),np.random.default_rng(10+k)))
