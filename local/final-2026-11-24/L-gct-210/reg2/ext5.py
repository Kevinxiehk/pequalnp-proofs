# survey of 5-dim level 4x5 spaces (extensions of known 3-,4-dim ones inside E_0) and their Omega: which have Omega = C^5 ?
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief')
import numpy as np, glob, time
from ext6 import *
from a1 import phirank
import core
seed=int(sys.argv[1]); tmax=float(sys.argv[2])
rg=np.random.default_rng(seed)
def Lr(B,r):
    m=np.ones((5,5),bool); m[r]=False
    S=sub_supported(B,m); rows=[i for i in range(5) if i!=r]
    return S[:,rows,:]
def info5(B,rg):
    B=onb(B)
    def part(mask):
        A=B.reshape(len(B),-1)[:,~mask.ravel()].T; sv=np.linalg.svd(A,compute_uv=False); return int((sv<1e-4).sum())+max(0,len(B)-len(sv))
    sr=[]; sc=[]
    for i in range(4):
        mk=np.zeros((4,5),bool); mk[i]=True; sr.append(part(mk))
    for j in range(5):
        mk=np.zeros((4,5),bool); mk[:,j]=True; sc.append(part(mk))
    ds=defect(B,n=60); e=int((ds>1e-4*ds[0]).sum())
    T=T1(embed(B),rg,npts=90,tol=1e-5); nT=len(T); S=np.linalg.svd(T[:,4,:],compute_uv=False); om=int((S>1e-5*S[0]).sum())
    ps=phirank(B); pr=int((ps>1e-4*max(ps[0],1e-3)).sum())
    E=E0(B,rg,tol=1e-5)
    return om,pr,'srow %s scol %s e=%d PhiRk=%d Om=%d T1=%d E0=%d'%(sr,sc,e,pr,om,nT,len(E))
bases=[]
for name in ('L080','ex1','ex2','ex3','fam2'):
    Bm=np.array([np.array(mm,dtype=complex) for mm in core.SP[name]()])
    for tr,Bt in (('row',Bm),('col',Bm.transpose(0,2,1))):
        for r in range(5):
            M=Lr(Bt,r)
            if len(M) in (3,4): bases.append(('%s %s %d'%(name,tr,r),onb(M)))
for f in sorted(glob.glob('../rows/clm_p4_d4_*.npy'))[:6]+sorted(glob.glob('../rows/clm_p4_d3_*.npy')): bases.append((f.split('/')[-1],onb(np.load(f))))
rg.shuffle(bases)
t0=time.time(); stats={}
for name,M in bases:
    if time.time()-t0>tmax: print('time limit'); break
    E=E0(M,rg); D=complement(M,E); q=len(D); m=5-len(M)
    if q<=m: continue
    outs=set()
    for trial in range(4):
        if time.time()-t0>tmax: break
        c,B=solve_ext(M,D,m,rg,iters=150,N=260)
        if c<1e-9:
            om,pr,desc=info5(B,rg); outs.add(desc); stats[(om,pr==0)]=stats.get((om,pr==0),0)+1
    print('%-26s dim %d q=%d:'%(name,len(M),q)); 
    for o in sorted(outs): print('     ',o)
    sys.stdout.flush()
print('STATS (dim Omega, Phi==0): count',stats)
