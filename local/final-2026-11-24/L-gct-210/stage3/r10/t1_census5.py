# Round 10: dim T_1(N) for every stored 5-dim 4x5 level space N (embedded in 5x5 with a zero row). A 9-dim level L with a_r = 1 has
# L_r = such an N and needs dim T_1(L_r) >= 10 (L inside T_1(L_r), y_r in T_1(L_r) but in no level space).
import sys, glob, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9')
import build7
from t1_c52 import T1, rank, single_rows, cofs
import itertools
def sig2(t):
    s_=t.sum(1); G=t@t.T; return (np.outer(s_,s_)-G)[np.triu_indices(5,1)].sum()
def fo2_0(B):
    d=len(B); rg=np.random.default_rng(2)
    A=np.array([cofs(np.ones((5,5))+np.tensordot((rg.normal(size=d)+1j*rg.normal(size=d))*0.7,B,axes=1)) for _ in range(150)])
    u,s_,vh=np.linalg.svd(A); r=int((s_>1e-7*s_[0]).sum()); T=vh[r:].conj().reshape(-1,5,5); n=len(T)
    Qm=np.array([[(sig2(T[i]+T[j])-sig2(T[i])-sig2(T[j]))/2 for j in range(n)] for i in range(n)])
    sv=np.linalg.svd(Qm,compute_uv=False); rk=int((sv>1e-7*sv[0]).sum()); return n,(n-rk)+rk//2
cnt={}
fs=sorted(glob.glob('/home/kevxhk/work/L-gct-210/rows/*.npy'))+sorted(glob.glob('/home/kevxhk/work/L-gct-210/stage3/r9/pr2_sol_*.npy'))+sorted(glob.glob('/home/kevxhk/work/L-gct-210/stage3/r10/pr2split_sol_*.npy'))
for f in fs:
    try: Z=np.load(f)
    except Exception: continue
    if Z.ndim!=3 or Z.shape[1:]!=(4,5) or len(Z)!=5: continue
    B=np.zeros((5,5,5),complex); B[:,:4,:]=Z
    if build7.check(B,n=3)>1e-6: continue
    t=T1(B); n_,b0=fo2_0(B); rp=tuple(sorted(rank(Z[:,r,:]) for r in range(4))); u=tuple(sorted(single_rows(Z),reverse=True))
    k=(t[0],b0,rp,u); cnt.setdefault(k,[]).append((f.split('/')[-1],'%.0e/%.0e'%(t[1],t[2])))
for k,v in sorted(cnt.items()): print('dim T_1 = %d  FO2_0 bound (max sigma_2-isotropic dim in T_1) = %d  row-proj %s  single-row %s : %d  e.g. %s'%(k[0],k[1],k[2],k[3],len(v),v[:1]))
print('MAX dim T_1 over %d spaces: %d ; MAX FO2_0 bound: %d'%(sum(len(v) for v in cnt.values()),max(k[0] for k in cnt),max(k[1] for k in cnt)))
