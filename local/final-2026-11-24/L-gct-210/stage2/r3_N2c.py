# Sanity for the reduction "X level <=> (i),(ii),(iii)": take LM solutions of (i)-(iii) (they all have a zero weight or a unit
# vector in P), build X = {(pi_c; a o pi_d; b o pi_e): pi_i in P, sum pi_i = 0} and test perm(J + t) = 120 on random t in X;
# and for random (P,a,b) (not solutions) check that perm(J+t) - 120 is NOT zero (the test is not vacuous).
import sys, itertools, numpy as np
from scipy.optimize import least_squares
src=open('/home/kevxhk/work/L-gct-210/stage2/r3_N2.py').read().split("stats={}; ex={}")[0]
sys.argv=[sys.argv[0],'3']; exec(src)
def perm(M):
    n=len(M); return sum(np.prod([M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n)))
def dev(lam,a,b,rg):
    worst=0
    for _ in range(6):
        c=rg.normal(size=(3,2))+1j*rg.normal(size=(3,2)); c[2]=-c[0]-c[1]; pis=c@lam.T   # three vectors of P with sum 0
        t=np.zeros((5,5),complex); t[2]=pis[0]; t[3]=a*pis[1]; t[4]=b*pis[2]
        worst=max(worst,abs(perm(np.ones((5,5))+t)-120))
    return worst
rg=np.random.default_rng(5); got=0; w=0
for trial in range(40):
    z=rg.normal(size=44); s=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=400)
    if np.linalg.norm(s.fun)>1e-10: continue
    lam,sig,a,b=unpack(s.x)
    if max(abs(a).max(),abs(b).max())>1e4: continue
    got+=1; w=max(w,dev(lam,a,b,rg))
print('solutions of (i)-(iii) tested:',got,'  max |perm(J+t)-120| on X:',w)
lam=rg.normal(size=(5,2))+1j*rg.normal(size=(5,2)); a=rg.normal(size=5)+0j; b=rg.normal(size=5)+0j
print('random (P,a,b), not a solution: |perm(J+t)-120| =',dev(lam,a,b,rg))
