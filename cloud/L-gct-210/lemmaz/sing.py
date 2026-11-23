import numpy as np, sys; sys.path.insert(0,"/home/claude/work/L-gct-210/lemmaz")
from core import *
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
# (0) one-sided counterexample: rows v,-v,e1,e1,-2e1
v=rng.normal(size=5)+1j*rng.normal(size=5); e1=np.eye(5)[0]
g=np.array([v,-v,e1,e1,-2*e1]); print("one-sided counterexample: |minors|max %.1e, |colsums| %.1e, min row/col norm %.2f %.2f"%(np.abs(minors(g)).max(),np.abs(g.sum(0)).max(),np.abs(g).max(1).min(),np.abs(g).max(0).min()))
# (1) torus form: sample Sing(perm_5) cap {det=0} without centring; look at kernels
def cof(g):
    out=np.zeros((5,5),complex)
    for i in range(5):
        for j in range(5):
            out[i,j]=(-1)**(i+j)*np.linalg.det(np.delete(np.delete(g,i,0),j,1))
    return out
for st in range(N):
    lam=rng.normal(size=25)+1j*rng.normal(size=25)
    F=lambda x: np.concatenate([minors(x.reshape(5,5)).ravel(),[np.linalg.det(x.reshape(5,5)),lam@x-1]])
    x,r=solve(F,rng.normal(size=25)+1j*rng.normal(size=25))
    g=x.reshape(5,5); g=g/np.abs(g).max()
    sv=np.linalg.svd(g,compute_uv=False); rk=int((sv>1e-6*sv[0]).sum())
    rn=np.abs(g).max(1); cn=np.abs(g).max(0)
    C=cof(g); C=C/max(np.abs(C).max(),1e-300)
    nz=int((np.abs(g)<1e-6).sum())
    print(st,"res %.0e rank %d zero rows %d cols %d zero entries %d"%(r,rk,int((rn<1e-6).sum()),int((cn<1e-6).sum()),nz),
          "| cofactor matrix: zero rows %d cols %d (rank-4 case: kernel supports)"%(int((np.abs(C).max(1)<1e-6).sum()),int((np.abs(C).max(0)<1e-6).sum())) if rk==4 else "")
