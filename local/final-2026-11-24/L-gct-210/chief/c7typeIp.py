import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief')
import numpy as np, itertools
from core import nullspace
from testAB_lib import rank, Qf
rng=np.random.default_rng(12)
def rnd(k): return rng.normal(size=k)+1j*rng.normal(size=k)
def check(n,kst,kp,label):
    # M = span{(n,0),(kst,-kp)} ; ell = <kp,z2>
    out=[]; allok=True
    for j,l in itertools.combinations(range(5),2):
        A=np.array([[n[j],n[l],0,0],[kst[j],kst[l],-kp[j],-kp[l]]])
        N=nullspace(A); ell=np.array([0,0,kp[j],kp[l]])@N
        G=N.T@Qf@N; rk=rank(G,1e-9); B1=abs(ell).max()>1e-9; ok=True
        if B1:
            ok = (N.shape[1]==2 and rk==1)
            if ok:
                k=nullspace(ell[None,:]); z=N@k[:,0]; ok=np.abs(N.T@Qf@z).max()<1e-8
        allok&=ok; out.append(((j,l),'B1' if B1 else 'nonB1',rk,'OK' if ok else 'FAIL'))
    print(label,'sum n=%.1e sum k*=%.2f sum k\'=%.2f'%(abs(n.sum()),abs(kst.sum()),abs(kp.sum())),'all pairs consistent with ThB:',allok)
    return out
# Type I': kp = kp1+kp2 with sums 1/2 each; n = kp1-kp2 ; k* = 2 kp2
kp=rnd(5); C1=[0,1,2]; C2=[3,4]
kp[C1]*=0.5/kp[C1].sum(); kp[C2]*=0.5/kp[C2].sum()
n=kp.copy(); n[C2]*=-1; kst=np.zeros(5,complex); kst[C2]=2*kp[C2]
check(n,kst,kp,"Type I'  ")
# generic (2,1): expect failures
kp=rnd(5); kp/=kp.sum(); n=rnd(5); n-=n.mean(); kst=rnd(5); kst/=kst.sum()
o=check(n,kst,kp,'generic  '); print('   generic sample:',o[:3])
