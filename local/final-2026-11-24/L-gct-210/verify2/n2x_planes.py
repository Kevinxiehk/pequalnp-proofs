# verify2: independent numerical probe of the algebraic core of stage3's Theorem N2-X.
# Five 2-planes P_a, P_b, P_c, P_d, P_e of C^5 with (Q4): P_a P_b P_k P_l = 0 in A_4 for the three pairs {k,l} of {c,d,e}.
# N2-X says: if moreover (NT) no three planes equal one coordinate plane, (NT') no two of P_c, P_d, P_e equal one coordinate plane, and the
# planes do not all lie in three columns, then P_c = P_d = P_e (case beta-0, which is killed by other conditions).
# Each plane is taken in a chart rowspace[I_2 | F] on a random pivot pair (so its two pivot columns are really used); LM on all 240 equations.
import numpy as np, itertools, sys, time
from scipy.optimize import least_squares
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0); tmax=float(sys.argv[2]) if len(sys.argv)>2 else 100
P4=list(itertools.permutations(range(4))); F4=list(itertools.combinations(range(5),4))
IDX=[]
for k,l in ((2,3),(2,4),(3,4)):
    for i in itertools.product(range(2),repeat=4):
        for F in F4:
            for p in P4:
                IDX.append([(0,i[0],F[p[0]]),(1,i[1],F[p[1]]),(k,i[2],F[p[2]]),(l,i[3],F[p[3]])])
IDX=np.array(IDX)                      # (5760, 4, 3)
def planes(z,piv):
    zc=z[:30]+1j*z[30:]; out=np.zeros((5,2,5),complex)
    for r in range(5):
        oth=[k for k in range(5) if k not in piv[r]]
        out[r,0,piv[r][0]]=1; out[r,1,piv[r][1]]=1; out[r][:,oth]=zc[6*r:6*r+6].reshape(2,3)
    return out
def res(z,piv):
    E=planes(z,piv)
    t=E[IDX[:,0,0],IDX[:,0,1],IDX[:,0,2]]*E[IDX[:,1,0],IDX[:,1,1],IDX[:,1,2]]*E[IDX[:,2,0],IDX[:,2,1],IDX[:,2,2]]*E[IDX[:,3,0],IDX[:,3,1],IDX[:,3,2]]
    r=t.reshape(-1,24).sum(axis=1); return np.concatenate([r.real,r.imag])
def same(P,Q): return np.linalg.matrix_rank(np.vstack([P,Q]),tol=1e-6)==2
def coord(P): return int(np.sum(np.abs(P).max(axis=0)>1e-6))==2
t0=time.time(); stat={}; n=0; examples=[]
while time.time()-t0<tmax:
    piv=[tuple(sorted(rng.choice(5,size=2,replace=False))) for _ in range(5)]
    sol=least_squares(res,rng.normal(size=60)*rng.choice([0.5,1.5]),args=(piv,),method='lm',max_nfev=400); n+=1
    if np.linalg.norm(sol.fun)>1e-9: stat['not converged']=stat.get('not converged',0)+1; continue
    P=planes(sol.x,piv)
    if max(np.abs(p).max() for p in P)>1e4: stat['chart blow-up']=stat.get('chart blow-up',0)+1; continue
    cols=int(np.sum(np.abs(np.vstack(P)).max(axis=0)>1e-6))
    nt=any(same(P[i],P[j]) and same(P[i],P[k]) and coord(P[i]) for i,j,k in itertools.combinations(range(5),3))
    ntp=any(same(P[k],P[l]) and coord(P[k]) for k,l in ((2,3),(2,4),(3,4)))
    b0=same(P[2],P[3]) and same(P[2],P[4])
    if cols<=3: key='all planes in three columns'
    elif nt: key='(NT) violated: three planes = one coordinate plane'
    elif ntp: key="(NT') violated"
    elif b0: key='P_c = P_d = P_e (beta-0)'
    else: key='GENUINE (contradicts N2-X core)'; examples.append(P)
    stat[key]=stat.get(key,0)+1
print('starts',n); [print('  %-55s %d'%(k,v)) for k,v in sorted(stat.items())]
np.set_printoptions(precision=3,suppress=True,linewidth=160)
for P in examples[:2]:
    for p in P: print(p)
    print()
