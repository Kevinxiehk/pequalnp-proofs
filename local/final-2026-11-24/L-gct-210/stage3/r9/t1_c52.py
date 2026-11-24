# Round 9: (S3-a) with e(L_e) = 2 has core M = L(L_e), L_e a (5,2) space WITHOUT single-row elements (z_r = 0, r in R), and every level
# L containing M lies in T_1(M). So "dim T_1(L(L')) <= 8 for all such L'" excludes this half of (S3-a). Numerical census of dim T_1.
import sys, glob, itertools
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/handoff')
import numpy as np, build7
P4=np.array(list(itertools.permutations(range(4))))
def cofs(M):
    out=[]
    for i in range(5):
        for j in range(5):
            A=np.delete(np.delete(M,i,axis=0),j,axis=1); out.append(A[np.arange(4)[None,:],P4].prod(axis=1).sum())
    return np.array(out)
def rank(A,tol=1e-7):
    s=np.linalg.svd(np.atleast_2d(A),compute_uv=False); return int((s>tol*max(1,s[0])).sum()) if s.size else 0
def T1(B,n=100,seed=1):
    rg=np.random.default_rng(seed); d=len(B)
    A=np.array([cofs(np.ones((5,5))+np.tensordot((rg.normal(size=d)+1j*rg.normal(size=d))*0.7,B,axes=1)) for _ in range(n)])
    s=np.linalg.svd(A,compute_uv=False); rk=int((s>1e-7*s[0]).sum()); return 25-rk, s[rk-1]/s[0], (s[rk]/s[0] if rk<25 else 0)
def single_rows(Z,tol=1e-6):   # dims of single-row parts of the 4x5 space Z (d,4,5)
    d=len(Z); out=[]
    for r in range(4):
        A=np.array([[Z[k][i,j] for k in range(d)] for i in range(4) if i!=r for j in range(5)]); out.append(d-rank(A,tol))
    return out
if __name__!="__main__": fs=[]
else: fs=sorted(set(glob.glob('/home/kevxhk/work/L-gct-210/rows/c52_*.npy')+glob.glob('/home/kevxhk/work/L-gct-210/rows/clm_p4_d5_defect2_*.npy')))
cnt={}
for f in fs:
    Z=np.load(f)
    if Z.ndim!=3 or Z.shape[1:]!=(4,5): print(f.split('/')[-1],'shape',Z.shape,'skipped'); continue
    B,e=build7.build(Z); lev=build7.check(B)
    if len(B)!=7 or lev>1e-6: print(f.split('/')[-1],'dim',len(B),'e',e,'level err %.1e skipped'%lev); continue
    u=single_rows(Z); t=T1(B); key=('no single-row' if sum(u)==0 else 'split u=%s'%sorted(u,reverse=True),t[0]); cnt[key]=cnt.get(key,0)+1
    print('%-28s e=%d single-row dims %s  dim T_1(L(L\')) = %d (gap %.0e / %.0e)'%(f.split('/')[-1],e,u,t[0],t[1],t[2]),flush=True)
if fs:
    print('SUMMARY (type, dim T_1): count')
    for k,v in sorted(cnt.items()): print('  ',k,v)
