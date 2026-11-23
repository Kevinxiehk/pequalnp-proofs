# Round 6: are rows' defect-form 7-dim spaces M = L' (+) e_5 (x) W valid "7-dim cores" for (S3), z_e = 2?
# Necessary for a 9-dim L with all a_r = 1 containing M as sum of the L_r: (CA2) all 4x4 subpermanents vanish on every M cap {row r = 0}.
import sys, glob, itertools
sys.path.insert(0,'/home/claude/work/L-gct-210/rows'); sys.path.insert(0,'/home/claude/work/L-gct-210/numerics'); sys.path.insert(0,'/home/claude/work/L-gct-210/chief')
import numpy as np, build7
P4=np.array(list(itertools.permutations(range(4))))
def rank(A,tol=1e-7):
    s=np.linalg.svd(np.atleast_2d(A),compute_uv=False); return int((s>tol*max(1,s[0])).sum()) if s.size else 0
def null(A,tol=1e-7):
    u,s,vh=np.linalg.svd(A); r=int((s>tol*max(1,s[0])).sum()); return vh[r:].conj().T
def sub4(M,rows):      # the five 4x4 subpermanents of the 4x5 matrix M[rows]
    X=M[rows]; return np.array([np.delete(X,j,axis=1)[np.arange(4)[None,:],P4].prod(axis=1).sum() for j in range(5)])
rg=np.random.default_rng(4)
for f in sorted(glob.glob('/home/claude/work/L-gct-210/rows/clm_p4_d[45]_defect[12]_s*.npy')):
    Z=np.load(f); B,e=build7.build(Z); d=len(B)
    if build7.check(B)>1e-6: continue
    out=[]
    for r in range(5):
        A=np.array([[B[k][r,j] for k in range(d)] for j in range(5)]); N=null(A)       # coefficients of M cap {row r = 0}
        rows=[i for i in range(5) if i!=r]; mx=0
        for _ in range(6):
            c=N@(rg.normal(size=N.shape[1])+1j*rg.normal(size=N.shape[1])); t=np.tensordot(c,B,axes=1)
            mx=max(mx,np.abs(sub4(t,rows)).max()/max(1e-12,np.abs(t).max()**4))
        out.append('%d:%.0e'%(N.shape[1],mx))
    rp=[rank(B[:,r,:]) for r in range(5)]
    print(f.split('/')[-1],'(dim L\',e)=(%d,%d)'%(len(Z),e),' row ranks of M',rp,' [dim(M cap row r = 0) : max |4x4 subperm|] per row:',' '.join(out))
