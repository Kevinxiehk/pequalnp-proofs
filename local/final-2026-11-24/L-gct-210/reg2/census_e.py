# CENSUS E (line-spanned part), calibrated version (reg2 round 4).  usage: census_e.py SEED SLICE NSLICES NSTARTS
#  Runs linespan.solve on the patterns of slice SLICE (of NSLICES) of the 45 support patterns (u | v), NSTARTS starts each.
#  For every hit (residual < 1e-9, rank 6, level error < 1e-8 at fresh points): single-row parts, full-free-row flag, deletable rows,
#  (dim Omega, dim T_1, FO2) at relative tolerances 1e-6 and 1e-9.  Output: one line per hit, a summary line per pattern (hit rate = calibration).
#  Hits WITHOUT a full free row and with FO2 >= 9 at both tolerances are saved as census_e_CAND_*.npy (decisive event: see COMPUTE-reg2 6).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, time
import linespan as LS
from t import level_err, rowpart, rank
from a1 import embed
from a5 import onb
from a6 import T1
from r5_FO2 import FO2
seed,sl,nsl,nst=map(int,sys.argv[1:5]); rg=np.random.default_rng(seed); LS.rg=rg
pats=[]
for k in range(0,7):
    for u in LS.parts(k,3,4):
        for v in LS.parts(6-k,3,5):
            pats.append((u+(0,)*(4-len(u)),v+(0,)*(5-len(v))))
mine=[p for i,p in enumerate(pats) if i%nsl==sl]
def inv(B,tol):
    T=T1(embed(B),rg,npts=200,tol=tol); U_,S,Vh=np.linalg.svd(T[:,4,:].T,full_matrices=False); r=int((S>tol*S[0]).sum())
    n,rk,bd=FO2(embed(B),np.random.default_rng(1),npts=200,tol=tol); return r,len(T),bd
for (u,v) in mine:
    t0=time.time(); hits=0
    for s in range(nst):
        c,B=LS.solve(u,v,rg)
        if not (c<1e-9 and np.linalg.matrix_rank(B.reshape(6,20),tol=1e-6)==6): continue
        Bo=onb(B)
        if level_err(Bo,ntest=40,seed=s+1000)>1e-8: continue
        hits+=1; sr=[len(rowpart(Bo,[i])) for i in range(4)]; ffr=max(sr)>=4
        a=inv(Bo,1e-6); b=inv(Bo,1e-9)
        print('HIT u=%s v=%s start %d: single-row parts %s fullfree %s (Omega,T1,FO2)@1e-6=%s @1e-9=%s'%(u,v,s,sr,ffr,a,b),flush=True)
        if (not ffr) and a[2]>=9 and b[2]>=9:
            np.save('census_e_CAND_s%d_%d_%d.npy'%(seed,pats.index((u,v)),s),Bo); print('   CANDIDATE saved',flush=True)
    print('PATTERN u=%s v=%s: %d hits / %d starts (%.0f s)'%(u,v,hits,nst,time.time()-t0),flush=True)
