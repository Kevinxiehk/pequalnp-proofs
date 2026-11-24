# find members of a (1,1,1,1,0) configuration where the outside-row kernel of pair PR jumps (an extra kernel vector xi orthogonal to the known
# kernel: gauge (W[l] on row l, W[n] on row n) and c (x) 1 on rows (4,l,n) with sum c = 0); then report the jump measures of all pairs.
import numpy as np, itertools, sys
MYARGS=sys.argv[1:4]; sys.argv=['x','7']
exec(open('/home/kevxhk/work/L-gct-210/stage3/r22/special_scan.py').read().split("nm=sys.argv[1]")[0])
nm,PR,NS=MYARGS[0],int(MYARGS[1]),int(MYARGS[2]); param,nv,extra=cfgs[nm]
nvar=nv+len(extra(np.zeros(nv+4,complex)))
pairs=list(itertools.combinations(range(4),2)); r,k=pairs[PR]; l,n=[i for i in range(4) if i not in (r,k)]
rg2=np.random.default_rng(11); NRM=rg2.normal(size=15)+1j*rg2.normal(size=15); RM=rg2.normal(size=(15,5))+1j*rg2.normal(size=(15,5))
def known(W):
    one=np.ones(5); z=np.zeros(5)
    return np.array([np.r_[z,W[l],z],np.r_[z,z,W[n]],np.r_[one,-one,z],np.r_[one,z,-one]])  # (v; a; b) ordering as in outside.py: v, a(row l), b(row n)
def F(y):
    x=y[:nvar]; xi=y[nvar:nvar+15]; W=np.array(param(x))
    A=pair_mats(W)[PR]
    Kx=np.vstack([known(W),xi]); return np.concatenate([srow_eqs(W),extra(x),A@xi,[y[-1]*np.linalg.det(Kx@RM)-1],[NRM@xi-1]])
def lm(y,it=300):
    lam=1e-2; N=len(y)
    for _ in range(it):
        f=F(y); nf=np.linalg.norm(f)
        if nf<1e-12: break
        Jm=np.array([(F(y+1e-7*np.eye(N)[i])-f)/1e-7 for i in range(N)]).T
        Am=Jm.conj().T@Jm; g=Jm.conj().T@f; ok=False
        for _ in range(10):
            dx=np.linalg.solve(Am+lam*np.eye(N),g)
            if np.linalg.norm(F(y-dx))<nf: y=y-dx; lam=max(lam/4,1e-15); ok=True; break
            lam*=4
        if not ok: break
    return y,np.linalg.norm(F(y))
rg3=np.random.default_rng(5)
for st in range(NS):
    y,nf=lm(rg3.normal(size=nvar+16)+1j*rg3.normal(size=nvar+16))
    if nf<1e-9:
        W=np.array(param(y[:nvar])); print('start %d res %.1e jump measures %s'%(st,nf,np.round(jump_measure(W),5)),flush=True)
        for i in range(4): print('   W[%d] = %s'%(i,np.round(W[i]/W[i][np.argmax(np.abs(W[i]))],4)),flush=True)
    else: print('start %d res %.1e'%(st,nf),flush=True)
