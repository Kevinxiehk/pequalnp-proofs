import numpy as np, itertools, time
from scipy.optimize import least_squares
# Sub-case (alpha, v_0 = e_j) of MIN-C: five nonzero vectors pi_i in C^4 with ALL triple products zero in the squarefree algebra
# (all 3x3 subpermanents of every three of them vanish). Claim: every solution violates (NZ) [supports do not cover the 4 columns]
# or (NT) [three vectors on one coordinate line]. Numerical corroboration: LM from random starts, classify the solutions found.
P3=list(itertools.permutations(range(3)))
TR=list(itertools.combinations(range(5),3)); CS=list(itertools.combinations(range(4),3))
TI=np.array([t for t in TR for c in CS]); CI=np.array([c for t in TR for c in CS])
def res(x):
    V=(x[:20]+1j*x[20:]).reshape(5,4); V=V/np.linalg.norm(V,axis=1)[:,None]
    A=V[TI[:,:,None],CI[:,None,:]]
    out=sum(A[:,0,p[0]]*A[:,1,p[1]]*A[:,2,p[2]] for p in P3)
    return np.concatenate([out.real,out.imag])
rng=np.random.default_rng(5); t0=time.time(); kinds={}; nsol=0
for s in range(120):
    if time.time()-t0>100: break
    sol=least_squares(res,rng.normal(size=40),method='lm',max_nfev=1500)
    if np.sqrt(2*sol.cost)>1e-9: continue
    nsol+=1
    V=(sol.x[:20]+1j*sol.x[20:]).reshape(5,4); V=V/np.linalg.norm(V,axis=1)[:,None]
    supp=np.abs(V)>1e-5
    covered=int(supp.any(axis=0).sum())
    unit=[tuple(r) for r in supp if r.sum()==1]
    max_same_unit=max([unit.count(u) for u in set(unit)],default=0)
    key=('columns covered: %d'%covered,'max #vectors on one coordinate line: %d'%max_same_unit,'support sizes: %s'%sorted(supp.sum(axis=1)))
    kinds[key]=kinds.get(key,0)+1
print('converged starts: %d of %d (%.0f s)'%(nsol,s+1,time.time()-t0))
bad=0
for k,v in sorted(kinds.items(),key=lambda kv:-kv[1]):
    viol = (k[0]!='columns covered: 4') or (int(k[1].split(': ')[1])>=3)
    bad+= (0 if viol else v)
    print('  ',v,k,'' if viol else '   <-- satisfies (NZ) and (NT): COUNTEREXAMPLE?')
print('solutions satisfying both (NZ) and (NT):',bad)
