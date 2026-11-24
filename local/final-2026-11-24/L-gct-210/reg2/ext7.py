# 7-dim 4x5 level spaces containing a known 3-,4-,5-dim level space M_b: (7-b)-planes in E_0(M_b)/M_b.  Calibration: target 6 (ext6.py).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief')
import numpy as np, glob, time
from ext6 import *
import core
seed=int(sys.argv[1]); tmax=float(sys.argv[2]); rg=np.random.default_rng(seed)
def Lr(B,r):
    m=np.ones((5,5),bool); m[r]=False
    S=sub_supported(B,m); rows=[i for i in range(5) if i!=r]
    return S[:,rows,:]
bases=[]
for f in sorted(glob.glob('../rows/clm_p4_d5_*.npy'))+sorted(glob.glob('../rows/clm_p4_d4_*.npy')): bases.append((f.split('/')[-1],onb(np.load(f))))
for name in ('L080','ex1','ex2','ex3','fam2'):
    Bm=np.array([np.array(mm,dtype=complex) for mm in core.SP[name]()])
    for tr,Bt in (('row',Bm),('col',Bm.transpose(0,2,1))):
        for r in range(5):
            M=Lr(Bt,r)
            if len(M) in (3,4,5): bases.append(('%s %s %d'%(name,tr,r),onb(M)))
rg.shuffle(bases); t0=time.time(); nb=0; ns=0; best=[]
for name,M in bases:
    if time.time()-t0>tmax: break
    E=E0(M,rg); D=complement(M,E); q=len(D); m=7-len(M)
    if q<m: continue
    nb+=1; res=[]
    if q==m:
        B=np.concatenate([M,D],0); res.append(level_err(onb(B)))
    else:
        for trial in range(3):
            c,B=solve_ext(M,D,m,rg,iters=120,N=330); res.append(c); ns+=1
    best.append(min(res))
    if min(res)<1e-8: print('FOUND 7-dim?',name,min(res)); np.save('cand7_%d.npy'%nb,B)
print('bases with room: %d, LM starts: %d, smallest residuals over bases: %s'%(nb,ns,np.array2string(np.sort(best)[:6],precision=2)))
