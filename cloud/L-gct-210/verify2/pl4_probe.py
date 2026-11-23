# verify2 round 4: independent numerical probe of stage3's Theorem PL4 (four 2-planes P_a..P_d and a vector w, s(w) = 0, |w| = 1, with
# (Q4) P_a P_b P_c P_d = 0, (QL) w P_k P_l P_m = 0 for the four triples, (NZ) all four triple products of norm >= delta).
# PL4 predicts: every solution is of type I (two planes equal to one coordinate plane containing w) or (3col) (planes and w in three columns).
import numpy as np, itertools, sys, time
from scipy.optimize import least_squares
seed=int(sys.argv[1]); nstart=int(sys.argv[2]); tmax=float(sys.argv[3]); NV=('nv4' in sys.argv)   # nv4: four chosen columns must not vanish
rng=np.random.default_rng(seed)
S4=list(itertools.combinations(range(5),4)); S3=list(itertools.combinations(range(5),3))
P4=list(itertools.permutations(range(4))); P3=list(itertools.permutations(range(3)))
T4=np.array(S4); T3=np.array(S3)
def coef4(G):      # G: (n,4,5) -> (n,5) coefficients of the product of the four rows in A_4
    out=0
    for p in P4:
        out=out+G[:,0,:][:,T4[:,p[0]]]*G[:,1,:][:,T4[:,p[1]]]*G[:,2,:][:,T4[:,p[2]]]*G[:,3,:][:,T4[:,p[3]]]
    return out
def coef3(G):      # (n,3,5) -> (n,10)
    out=0
    for p in P3:
        out=out+G[:,0,:][:,T3[:,p[0]]]*G[:,1,:][:,T3[:,p[1]]]*G[:,2,:][:,T3[:,p[2]]]
    return out
combos4=list(itertools.product(range(2),repeat=4)); combos3=list(itertools.product(range(2),repeat=3))
triples=[(1,2,3),(0,2,3),(0,1,3),(0,1,2)]
delta=0.5
def unpack(z,charts):
    X=(z[:24]+1j*z[24:48]).reshape(4,2,3); w=z[48:53]+1j*z[53:58]; sl=z[58:66]
    P=np.zeros((4,2,5),complex)
    for r in range(4):
        piv,rest=charts[r]; P[r][:,piv]=np.eye(2); P[r][:,rest]=X[r]
    return P,w,sl
def res(z,charts):
    P,w,sl=unpack(z,charts)
    G=[np.stack([P[0][i],P[1][j],P[2][k],P[3][l]]) for (i,j,k,l) in combos4]
    for (k,l,m) in triples:
        G+=[np.stack([w,P[k][i],P[l][j],P[m][n]]) for (i,j,n) in combos3]
    c=coef4(np.array(G)).ravel()
    out=[c.real,c.imag]
    for t,(k,l,m) in enumerate(triples):
        K=coef3(np.array([np.stack([P[k][i],P[l][j],P[m][n]]) for (i,j,n) in combos3])).ravel()
        out.append([np.vdot(K,K).real-delta**2-sl[t]**2])
    out.append([np.vdot(w,w).real-1, w.sum().real, w.sum().imag])
    if NV:
        cn=(np.abs(P)**2).sum(axis=(0,1))
        out.append([cn[j]-0.05-sl[4+t]**2 for t,j in enumerate(charts[4])])
    return np.concatenate([np.ravel(o) for o in out])
def classify(P,w,tol=1e-6):
    colnorm=np.sqrt((np.abs(P)**2).sum(axis=(0,1))+np.abs(w)**2)
    van=[j for j in range(5) if colnorm[j]<tol]
    planecols=[tuple(j for j in range(5) if np.linalg.norm(P[r][:,j])>tol) for r in range(4)]
    wsupp=tuple(j for j in range(5) if abs(w[j])>tol)
    if len(van)>=2: return '(3col): planes and w in three columns'
    for r in range(4):
        for s in range(r+1,4):
            if len(planecols[r])==2 and planecols[r]==planecols[s] and set(wsupp)<=set(planecols[r]): return 'type I: two planes = C^T, w in C^T'
    return 'OTHER (not predicted by PL4): plane supports %s, supp w %s'%(planecols,wsupp)
from collections import Counter
cnt=Counter(); t0=time.time(); done=0
for st in range(nstart):
    if time.time()-t0>tmax: break
    charts=[]
    for r in range(4):
        piv=sorted(rng.choice(5,2,replace=False)); charts.append((piv,[j for j in range(5) if j not in piv]))
    charts.append(sorted(rng.choice(5,4,replace=False)))
    z0=np.concatenate([rng.normal(size=48)*0.8,rng.normal(size=10)*0.5,rng.normal(size=8)])
    s=least_squares(res,z0,args=(charts,),method='lm',xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=400)
    done+=1; nrm=np.linalg.norm(s.fun)
    if nrm>1e-9 or np.abs(s.x[:48]).max()>1e3: cnt['not converged (residual > 1e-9 or blow-up)']+=1; continue
    P,w,sl=unpack(s.x,charts); c=classify(P,w); cnt[c]+=1; print('start',st,':',c,'(residual %.0e, %.0f s)'%(nrm,time.time()-t0),flush=True)
    if c.startswith('OTHER'): print('OTHER at start',st,'residual %.1e'%nrm); print(np.round(P,4)); print(np.round(w,4),flush=True)
print('seed',seed,'starts',done,'time %.0f s'%(time.time()-t0))
for k,v in cnt.items(): print('  %-60s %d'%(k,v))
