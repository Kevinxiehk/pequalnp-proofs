# Sanity for Theorem PFR: L level 5x5 containing e_i (x) U.  L0 := {t in L : t_i in U} = e_i (x) U (+) Pi, Pi := L0 cap {row i = 0} is a
# 4x5 level space with defect inside U^perp cap 1^perp.  Test on 7-dim level spaces L = M* (+) C t found by ext55 (M* = Mstar2.npy, i = 3),
# and report m and the split pair for the DR(3) spaces of drsearch.
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
import numpy as np, glob
from t import *
from a1 import embed, defect, pk
from a5 import onb
from a6 import T1
from ext55 import solve55
np.set_printoptions(precision=3,suppress=True,linewidth=200)
rg=np.random.default_rng(3)
B=onb(np.load('Mstar2.npy')); Mb=embed(B); T=T1(Mb,rg,npts=100)
Q,_=np.linalg.qr(Mb.reshape(6,25).T); Tm=T.reshape(len(T),25); X=Tm-(Tm@Q.conj())@Q.T
u,s,vh=np.linalg.svd(X); r=int((s>1e-7).sum()); D=vh[:r].reshape(r,5,5)
found=0
for trial in range(8):
    c,L=solve55(Mb,D,1,rg)
    if c>1e-10: continue
    found+=1; L=onb(L)
    # row 3 projection, U = {sum w = 0, w_1 = w_2}
    W3=L[:,3,:]; rk=rank(W3)
    A=np.array([np.ones(5),np.eye(5)[1]-np.eye(5)[2]])
    cond=(W3@A.T)                       # (7,2): conditions t_3 in U
    C=null(cond.T); L0=np.einsum('kc,cab->kab',C,L)
    # Pi = L0 cap {row 3 = 0}
    mk=np.ones((5,5),bool); mk[3]=False; Pi=sub_supported(L0,mk)
    Pi45=Pi[:,[0,1,2,4],:]              # rows 0,1,2 and r=4
    ds=defect(onb(Pi45),n=40); e=int((ds>1e-7*max(ds[0],1)).sum())
    # defect direction
    rng=np.random.default_rng(1); V=np.array([pk(np.einsum('k,kab->ab',rng.normal(size=len(Pi45))+1j*rng.normal(size=len(Pi45)),Pi45),k) for _ in range(5) for k in (1,2,3,4)])
    uu,ss,vv=np.linalg.svd(V); d=vv[0].conj()/vv[0].conj()[np.argmax(abs(vv[0]))]
    print('7-dim L: row-3 rank %d, dim L0 %d, dim Pi %d, level err of Pi %.0e, e(Pi) = %d, defect direction %s'%(rk,len(L0),len(Pi45),level_err(onb(Pi45),ntest=30),e,np.array2string(d,precision=2)))
print('7-dim extensions analysed:',found)
for f in sorted(glob.glob('dr_u3_s*.npy')):
    if '_lim' in f: continue
    Bo=onb(np.load(f)); mk=np.zeros((4,5),bool); mk[3]=True; SR=sub_supported(Bo,mk); Um=SR[:,3,:]
    if len(SR)!=3: print(f,'single-row part of row 3 has dim',len(SR)); continue
    # m spans {1,U}^perp cap 1^perp: vectors orthogonal (bilinear) to U and to 1
    A=np.concatenate([Um,np.ones((1,5))],0); m=null(A)[0]; m=m/m[np.argmax(abs(m))]
    # does M contain e_i m^T for some row i ?
    hit=[]
    for i in range(3):
        mk=np.zeros((4,5),bool); mk[i]=True; S=sub_supported(Bo,mk)
        for el in S:
            v=el[i]; cs=abs(np.vdot(m.conj(),v))  # bilinear pairing with m? check proportionality instead
            if rank(np.array([v,m]),1e-6)==1: hit.append(i)
    print('%s: m = %s, <m,m> = %s, zeros of m %d, rows with e_i m^T in M: %s, dim(U o m) = %d'%(f,np.array2string(m,precision=3),np.array2string((m*m).sum(),precision=3),int((abs(m)<1e-7).sum()),hit,rank(Um*m[None,:],1e-7)))
