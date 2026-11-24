# Round 10: is T_1(N) (dim 9) level?  N = 5-dim 4x5 example embedded with zero row 4. Also: FO2-type check (q_m isotropy on T_1/N).
import sys, glob, itertools, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9'); from t1_c52 import cofs, rank
P5=np.array(list(itertools.permutations(range(5))))
def perm5(X): return X[np.arange(5)[None,:],P5].prod(axis=1).sum()
for f in ['/home/kevxhk/work/L-gct-210/stage3/r9/pr2_sol_3_8.npy','/home/kevxhk/work/L-gct-210/stage3/r10/pr2split_sol_1_0.npy']:
    Z=np.load(f); d=len(Z); B=np.zeros((d,5,5),complex); B[:,:4,:]=Z; rg=np.random.default_rng(1)
    A=np.array([cofs(np.ones((5,5))+np.tensordot((rg.normal(size=d)+1j*rg.normal(size=d))*0.7,B,axes=1)) for _ in range(120)])
    u,s,vh=np.linalg.svd(A); r=int((s>1e-7*s[0]).sum()); T=vh[r:].conj().reshape(-1,5,5)      # T_1 basis (bilinear null space)
    errs=[abs(perm5(np.ones((5,5))+np.tensordot(rg.normal(size=len(T))+1j*rg.normal(size=len(T)),T,axes=1))-120) for _ in range(20)]
    # extra directions: T_1 modulo N; P_2-type test on them
    print(f.split('/')[-1],'dim T_1 =',len(T),' level error of T_1 at random points: median %.1e  min %.1e'%(np.median(errs),min(errs)))
    # does T_1 contain N? (sanity)
    Nv=B.reshape(d,-1); Tv=T.reshape(len(T),-1); print('   rank [T_1; N] =',rank(np.concatenate([Tv,Nv]),1e-6),' (= dim T_1 if N inside)')
    # is y_4 = e_4 1^T - J/5 in T_1 ?
    y=np.zeros((5,5)); y[4,:]=1; y-=1/5; print('   y_4 in T_1:',rank(np.concatenate([Tv,y.reshape(1,-1)]),1e-6)==len(T))
