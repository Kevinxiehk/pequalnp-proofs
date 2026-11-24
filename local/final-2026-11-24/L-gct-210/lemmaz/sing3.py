import numpy as np, sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/lemmaz")
from core import *
np.set_printoptions(precision=2,suppress=False,linewidth=220)
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
cnt={}
for st in range(N):
    lam=rng.normal(size=25)+1j*rng.normal(size=25)
    F=lambda x: np.concatenate([minors(x.reshape(5,5)).ravel(),[np.linalg.det(x.reshape(5,5)),lam@x-1]])
    x,r=solve(F,rng.normal(size=25)+1j*rng.normal(size=25),nfev=6000)
    g=x.reshape(5,5); g=g/np.abs(g).max()
    U,S,Vh=np.linalg.svd(g)
    rk=int((S>1e-3*S[0]).sum()); gap=S[rk]/S[0] if rk<5 else 1.0
    clean = r<1e-14 and rk<5 and gap<1e-8
    rn=np.abs(g).max(1); cn=np.abs(g).max(0)
    zl=int((rn<1e-7).sum()+(cn<1e-7).sum())
    if not clean: key="unclean"; 
    else:
        # distance of e_j to row space / e_i to column space
        Rs=Vh[:rk].conj().T; Cs=U[:,:rk]
        dr=[np.linalg.norm(np.eye(5)[j]-Rs@(Rs.conj().T@np.eye(5)[j])) for j in range(5)]
        dc=[np.linalg.norm(np.eye(5)[i]-Cs@(Cs.conj().T@np.eye(5)[i])) for i in range(5)]
        right_full = min(dr)>1e-6   # no e_j in row space  <=> right kernel has a full-support vector
        left_full = min(dc)>1e-6
        key="rank%d zero-lines %d rightkernel-full %s leftkernel-full %s"%(rk,zl,right_full,left_full)
        if zl==0 and right_full and left_full:
            print("CANDIDATE COUNTEREXAMPLE run",st,"res",r,"sv",S); print(np.abs(g)); np.save("cand_%s_%d.npy"%(sys.argv[1],st),g)
    cnt[key]=cnt.get(key,0)+1
for k in sorted(cnt): print(cnt[k],k)
