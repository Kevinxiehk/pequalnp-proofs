# verify2 round 5: do verifyfl's undersampled searches return spurious hits?  (r3_z.search: 28 points for k = 3, 44 for k = 4)
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/verifyfl')
import numpy as np, time, io, contextlib
buf=io.StringIO()
with contextlib.redirect_stdout(buf):
    import r3_z, di_ext
k=int(sys.argv[1]); tmax=float(sys.argv[2]); seed=int(sys.argv[3])
for nm,m in (('two-column (1,-1,0,0,0)',np.array([1,-1,0,0,0.])),('(1,2,-3,0,0)',np.array([1,2,-3,0,0.]))):
    t0=time.time(); hits,n,t=r3_z.search(k,m,200,seed,tmax)
    errs=[di_ext.chk_m(B,m,trials=300,seed=99) for B in hits]
    print('k = %d, m = %s: %d hits in %d starts (%.0f s); defect-in-Cm error at 300 FRESH points: %s'%(k,nm,len(hits),n,t,['%.1e'%e for e in errs]),flush=True)
