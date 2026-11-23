import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/reg2'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2'); sys.path.insert(0,'/home/claude/work/L-gct-210/chief')
import numpy as np, glob
from t import *
from a1 import embed
from a5 import onb, rref_tol
from a6 import E0
from a10 import Lr
from show import rref
import core
np.set_printoptions(precision=3,suppress=True,linewidth=200)
rg=np.random.default_rng(3)
def P2(Y):
    s=Y.sum(); return 0.5*(s*s-(Y.sum(1)**2).sum()-(Y.sum(0)**2).sum()+(Y**2).sum())
def test(M,name):
    E=E0(M,rg); # extra direction: complement of M in E0
    Mb=M.reshape(len(M),20); Q,_=np.linalg.qr(Mb.T); Ev=E.reshape(len(E),20); X=Ev-(Ev@Q.conj())@Q.T
    u,s,vh=np.linalg.svd(X); r=int((s>1e-7).sum()); D=vh[:r].reshape(r,4,5)
    msg=''
    for d in D:
        d=d/np.abs(d).max()
        # is it rank one x (x) 1 ?
        rowconst=np.abs(d-d.mean(1,keepdims=True)).max()
        msg+=' [extra dir: row-constant err %.1e, row means %s, P2(d)=%s, sum=%s]'%(rowconst,np.array2string(d.mean(1),precision=3,suppress_small=True),np.array2string(P2(d),precision=3),np.array2string(d.sum(),precision=2))
    print('%-26s dim M %d dim E0 %d%s'%(name,len(M),len(E),msg))
fs=sorted(glob.glob('../rows/rc45.npy')+glob.glob('../rows/clm_p4_d6_*.npy')+glob.glob('../rows/nc_d6_*.npy')+glob.glob('../rows/seed_d6_*.npy'))
for f in fs:
    B0=np.load(f); B=onb(rref_tol(onb(B0),1e-5))
    if level_err(B)>1e-9: continue
    test(B,f.split('/')[-1])
for name,tr,r in [('L080','col',0),('ex2','row',4),('ex3','row',4),('fam2','row',4),('L080','row',0),('ex2','col',2),('ex3','col',0)]:
    Bm=np.array([np.array(m,dtype=complex) for m in core.SP[name]()]); Bt=Bm if tr=='row' else Bm.transpose(0,2,1)
    test(onb(Lr(Bt,r)),'%s %s %d'%(name,tr,r))
