import sys,time,itertools; seed=int(sys.argv[1]); TL=float(sys.argv[2]); sys.argv=['x','1','A','1','10','50']; sys.path.insert(0,"/home/claude/work/L-gct-210/stage3")
import numpy as np, f4b_core as F
from scipy.optimize import least_squares
rng=np.random.default_rng(seed)
T0=time.time(); n=0; ns=0; best=[]
while time.time()-T0<TL:
    n+=1; t=time.time(); sol=least_squares(F.res,rng.normal(size=100)*0.6,method='lm',max_nfev=160); c=np.sqrt(2*sol.cost); best.append(c)
    print('start',n,'nfev',sol.nfev,'time %.1f'%(time.time()-t),'cost %.2e'%c,flush=True)
    if c<1e-8:
        ns+=1; z=sol.x[:50]+1j*sol.x[50:]; v,B=F.basis(z); nr=np.sqrt((np.abs(v)**2).sum(axis=1))
        print('SOL',n,'norms',np.round(nr,2),'sv',[round(F.sv2(v[r],v[6+r]),3) for r in range(4)],'sv(p,w) %.3f'%F.sv2(v[4],v[5]),'dim',F.rank(B.reshape(7,25)),'a_r',[5-F.rank(B[:,r,:]) for r in range(5)],flush=True)
        np.save('f4b_A1_sol_%d_%d.npy'%(seed,n),sol.x)
print('seed',seed,'starts',n,'solutions',ns,'residual quantiles',np.round(np.quantile(best,[0,0.1,0.5]),5),flush=True)
