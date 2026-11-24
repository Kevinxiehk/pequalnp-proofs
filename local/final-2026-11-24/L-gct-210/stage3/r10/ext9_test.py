# Round 10: can a (2,1,0,0)/(2,2,2,2) space N with dim T_1(N) = 10 be L_r of a 9-dim level space L?  L must be a hyperplane of T_1(N)
# containing N (and not y_r). Necessary: L inside ker sigma_1; L totally isotropic for sigma_2 (max isotropic dim in T_1 must be >= 9).
import sys, glob, itertools, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9'); from t1_c52 import cofs, rank
P5=np.array(list(itertools.permutations(range(5))))
def perm5(X): return X[np.arange(5)[None,:],P5].prod(axis=1).sum()
def sig2(t):  # sigma_2 of a 5x5 matrix: sum over row pairs of (s_i s_k - <t_i,t_k>)
    s=t.sum(1); G=t@t.T; return (np.outer(s,s)-G)[np.triu_indices(5,1)].sum()
for f in sys.argv[1:]:
    Z=np.load(f); d=len(Z); B=np.zeros((d,5,5),complex); B[:,1:,:]=Z; rg=np.random.default_rng(2)    # zero row 0
    A=np.array([cofs(np.ones((5,5))+np.tensordot((rg.normal(size=d)+1j*rg.normal(size=d))*0.7,B,axes=1)) for _ in range(150)])
    u,s,vh=np.linalg.svd(A); r=int((s>1e-7*s[0]).sum()); T=vh[r:].conj().reshape(-1,5,5); n=len(T)
    s1=np.array([t.sum() for t in T])                                        # sigma_1 on T_1
    Qm=np.array([[ (sig2(T[i]+T[j])-sig2(T[i])-sig2(T[j]))/2 for j in range(n)] for i in range(n)])
    sv=np.linalg.svd(Qm,compute_uv=False); rk=int((sv>1e-7*sv[0]).sum())
    print(f.split('/')[-1],'dim T_1',n,' |sigma_1 on T_1| max %.1e'%np.abs(s1).max(),' rank sigma_2 on T_1 = %d (sv %s)'%(rk,np.round(sv[:4],4)),
          ' max isotropic dim = %d'%((n-rk)+rk//2))
    if np.abs(s1).max()>1e-6:
        K=np.linalg.svd(s1[None,:])[2][1:].T; H=np.tensordot(K.T,T,axes=1)   # T_1 cap ker sigma_1
        e=[abs(perm5(np.ones((5,5))+np.tensordot(rg.normal(size=len(H))+1j*rg.normal(size=len(H)),H,axes=1))-120) for _ in range(10)]
        print('   T_1 cap ker sigma_1 (dim %d) level error median %.1e'%(len(H),np.median(e)))
