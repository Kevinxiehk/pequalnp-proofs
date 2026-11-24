# Round 6: first-order extension test (stage2's T_1) on rows' defect-form spaces M = L' (+) e_5 (x) (C(L') + C1)^perp.
import sys, glob, itertools
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/numerics'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief')
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
def T1dim(B,n=80,seed=1):
    rg=np.random.default_rng(seed); d=len(B)
    A=np.array([cofs(np.ones((5,5))+np.tensordot((rg.normal(size=d)+1j*rg.normal(size=d))*0.7,B,axes=1)) for _ in range(n)])
    s=np.linalg.svd(A,compute_uv=False); rk=int((s>1e-7*s[0]).sum()); return 25-rk, s[rk-1]/s[0], (s[rk]/s[0] if rk<len(s) else 0)
def info(B):
    d=len(B); R5=range(5)
    a=[5-rank(B[:,r,:]) for r in R5]
    def ker(rows):
        A=np.array([[B[k][i,j] for k in range(d)] for i in rows for j in R5]); return d-rank(A)
    Lr=[ker([r]) for r in R5]; z=[ker([i for i in R5 if i!=r]) for r in R5]
    lam=[ker([r,q]) for r in R5 for q in R5 if q>r]
    return a,Lr,z,lam
for f in sorted(glob.glob('/home/kevxhk/work/L-gct-210/rows/clm_p4_d*_defect*_s*.npy')):
    Z=np.load(f); B,e=build7.build(Z)
    if build7.check(B)>1e-6: print(f.split('/')[-1],'not level'); continue
    t1=T1dim(B); a,Lr,z,lam=info(B)
    print(f.split('/')[-1],'(dim L\',e) = (%d,%d)'%(len(Z),e),'dim M =',len(B),' dim T_1(M) =',t1[0],'(gap %.0e / %.0e)'%(t1[1],t1[2]),' a_r',a,' dim L_r',Lr,' z_r',z,' lam',lam)
