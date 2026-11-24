# check: for FK blocks K (3x3, 2x4, 4x2, rows, cols), grad P5 on M_K = L cap {zero on K} is supported on K and lies in Ann_K (sum-zero part)
import numpy as np, itertools, sys
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/methods'); import spaces
P=list(itertools.permutations(range(5)))
def perm(A): return sum(np.prod([A[i,p[i]] for i in range(A.shape[0])]) for p in itertools.permutations(range(A.shape[0])))
def gradP5(x):
    g=np.zeros((5,5),complex)
    for i in range(5):
        for j in range(5):
            g[i,j]=perm(np.delete(np.delete(x,i,0),j,1))
    return g
def nullspace(A,tol=1e-9):
    u,s,vh=np.linalg.svd(A); r=np.sum(s>tol); return vh[r:].conj().T
rng=np.random.default_rng(0)
for name in ['L080','ex1','ex2']:
    B=getattr(spaces,name)(); B=np.linalg.svd(B,full_matrices=False)[2][:np.linalg.matrix_rank(B,1e-9)]
    k=len(B); T=B.reshape(k,5,5); worst=0; stats={}
    blocks=[]
    for R in itertools.combinations(range(5),3):
        for C in itertools.combinations(range(5),3): blocks.append(('3x3',R,C))
    for R in itertools.combinations(range(5),2):
        for C in itertools.combinations(range(5),4): blocks.append(('2x4',R,C)); blocks.append(('4x2',C,R))
    for r in range(5): blocks.append(('row',(r,),tuple(range(5)))); blocks.append(('col',tuple(range(5)),(r,)))
    for typ,R,C in blocks:
        mask=np.zeros((5,5),bool); mask[np.ix_(R,C)]=True
        PK=T[:,mask]  # k x |K|
        Ann=nullspace(PK.T)  # |K| x a  (vectors n with PK n = 0)  -- careful: annihilator under bilinear pairing
        Ann=nullspace(PK) if False else None
        # bilinear annihilator: n in C^K with sum_e x_e n_e = 0 for all x in L  <=>  PK @ n = 0
        u,s,vh=np.linalg.svd(PK); r=np.sum(s>1e-9); AnnK=vh[r:].T  # columns: n with PK n=0 (complex: PK@vh.T? fix below)
        AnnK=nullspace(PK)  # PK @ n = 0 via svd of PK: null vectors are conj rows of vh
        AnnK=np.linalg.svd(PK)[2][r:].conj().T
        Mk=nullspace(PK.T.T) if False else None
        # M_K = combos c with sum_k c_k T_k zero on K: c in left-null of PK: PK^T c = 0
        Mc=np.linalg.svd(PK.T)[2][np.sum(np.linalg.svd(PK.T)[1]>1e-9):].conj().T
        if Mc.shape[1]==0: continue
        for t in range(3):
            c=Mc@(rng.normal(size=Mc.shape[1])+1j*rng.normal(size=Mc.shape[1]))
            x=np.tensordot(c,T,1); g=gradP5(x)
            off=abs(g[~mask]).max()
            gk=g[mask]; 
            # residual of gk in span(AnnK)
            if AnnK.shape[1]>0:
                co=np.linalg.lstsq(AnnK,gk,rcond=None)[0]; res=np.linalg.norm(AnnK@co-gk)
            else: res=np.linalg.norm(gk)
            worst=max(worst,off,res,abs(gk.sum()))
        stats[typ]=stats.get(typ,0)+1
    print(name,'dim',k,'blocks with M_K!=0:',stats,'worst violation %.1e'%worst)
