# local dimension of the K' variety at census hits: re-solve the same seed, then nullity of the Jacobian (cc3_search problem, chart variables)
import sys, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/ncol'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import cc3_search as cs
from clm import solve
for s in [int(a) for a in sys.argv[1:]]:
    Pr=cs.P(3,1,s); z,c=solve(Pr,iters=200,tol=1e-12)
    r,J=Pr.fun(z); sv=np.linalg.svd(J,compute_uv=False)
    null=(sv<1e-7*sv[0]).sum()+max(0,Pr.nvar-len(sv))
    print('seed %d res %.1e nvar %d  smallest sv %s  nullity(1e-7) %d'%(s,c,Pr.nvar,' '.join('%.1e'%v for v in sv[-8:]/sv[0]),null),flush=True)
