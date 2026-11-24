import numpy as np, itertools, time
from scipy.optimize import least_squares
# Safety check of MIN-C / MIN-D: search for five 2-planes P_1..P_5 of C^5 with (Q4) P_aP_bP_cP_d = 0 in A_4 for ALL five 4-sets,
# with every column nonzero (NZ) and without three planes equal to one coordinate plane (NT). The theorem says: none exist.
P4=np.array(list(itertools.permutations(range(4))))
SETS=list(itertools.combinations(range(5),4))
rows_i=[];rows_e=[];cols=[]
for S in SETS:
    for eps in itertools.product(range(2),repeat=4):
        for m in range(5):
            rows_i.append(S); rows_e.append(eps); cols.append([c for c in range(5) if c!=m])
RI=np.array(rows_i); RE=np.array(rows_e); CO=np.array(cols)          # (400,4)
def planes(x): return (x[:50]+1j*x[50:]).reshape(5,2,5)
def q4(A):
    Mx=A[RI[:,:,None],RE[:,:,None],CO[:,None,:]]                      # (400,4,4)
    return sum(Mx[:,0,p[0]]*Mx[:,1,p[1]]*Mx[:,2,p[2]]*Mx[:,3,p[3]] for p in P4)
def res(x,w=3.0):
    A=planes(x); r=q4(A)
    G=np.einsum('iaj,ibj->iab',A,A.conj())-np.eye(2)[None]            # rows of each plane orthonormal (gauge)
    cn=np.sqrt((np.abs(A)**2).sum(axis=(0,1)))                         # column norms
    hinge=w*np.maximum(0,0.45-cn)                                      # (NZ): every column of size >= 0.45
    Pr=np.einsum('iaj,iak->ijk',A.conj(),A)                            # projectors (rows ~ orthonormal)
    d=np.array([np.linalg.norm(Pr[i]-Pr[k]) for i in range(5) for k in range(i)])
    sep=w*np.maximum(0,DMIN-d)                                         # planes pairwise distinct (distance >= DMIN)
    return np.concatenate([r.real,r.imag,G.real.ravel(),G.imag.ravel(),hinge,sep])
import sys
DMIN=float(sys.argv[1]) if len(sys.argv)>1 else 0.6
rng=np.random.default_rng(22); t0=time.time(); nconv=0; best=[]; kinds={}
for s in range(400):
    if time.time()-t0>110: break
    sol=least_squares(res,rng.normal(size=100)*0.6,method='lm',max_nfev=1500)
    c=np.sqrt(2*sol.cost); best.append(c)
    if c<1e-8:
        nconv+=1; A=planes(sol.x); cn=np.sqrt((np.abs(A)**2).sum(axis=(0,1)))
        supp=[tuple((np.abs(A[i])>1e-5).any(axis=0).astype(int)) for i in range(5)]
        coord=[s_ for s_ in supp if sum(s_)==2]; nt=max([coord.count(c_) for c_ in set(coord)],default=0)
        key=('min column norm %.2f'%cn.min(),'max #equal coordinate planes %d'%nt)
        kinds[key]=kinds.get(key,0)+1
print('pairwise plane distance >= %.2f: starts %d, zero-residual solutions with all columns >= 0.45: %d   (%.0f s)'%(DMIN,s+1,nconv,time.time()-t0))
print('residual quantiles (min, 10%%, median): %.2e %.2e %.2e'%(min(best),np.quantile(best,0.1),np.median(best)))
for k,v in kinds.items(): print('  ',v,k)
