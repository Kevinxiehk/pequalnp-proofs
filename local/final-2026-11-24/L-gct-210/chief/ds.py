import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief')
from core import *
from testAB_lib import sub_with_zero
rng=np.random.default_rng(4)
def deletable(B,line,idx):
    worst=0
    for _ in range(4):
        c=rng.normal(size=len(B))+1j*rng.normal(size=len(B)); t=np.tensordot(c,B,1).copy()
        if line=='row': t[idx,:]=0
        else: t[:,idx]=0
        worst=max(worst,abs(perm(np.ones((5,5))+t)-120))
    return worst
for name,f in SP.items():
    B=f()
    dl=[('row',i) for i in range(5) if deletable(B,'row',i)<1e-8]+[('col',j) for j in range(5) if deletable(B,'col',j)<1e-8]
    out=[]
    for (line,i) in dl:
        Bt=B if line=='row' else np.transpose(B,(0,2,1))
        proj=np.linalg.matrix_rank(Bt[:,i,:])
        N=sub_with_zero(Bt,[(i,j) for j in range(5)]); k=N.shape[1]
        rows=[a for a in range(5) if a!=i]; dev=0
        for _ in range(3):
            if k==0: break
            c=N@(rng.normal(size=k)+1j*rng.normal(size=k)); x=np.tensordot(c,Bt,1)
            g=np.array([perm(np.ones((4,4))+x[np.ix_(rows,[m for m in range(5) if m!=j])]) for j in range(5)])
            dev=max(dev,np.abs(g-24).max())
        out.append((line,i,'dim proj',proj,'dim L_r',k,'max|g-24| %.1e'%dev))
    print(name,out)
