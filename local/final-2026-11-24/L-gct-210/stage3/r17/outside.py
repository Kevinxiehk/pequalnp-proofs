# Round 17: OUTSIDE-ROW LINEAR SYSTEM for z = (1,1,1,1,0): xi = (v on row 5; a on row l; b on row n) in X_{rk} must satisfy
#   < v + [l not in T] a + [n not in T] b , D(w_T) > = 0 for all T in S = {r,k,l,n}, D(w_T) = deletion vector of the rows w_i (i in T)
# (computed by brute force).  Kernel always contains the gauge (a = w_l, b = w_n); kernel dim 2 => lam_{rk} = 2 < 3: contradiction.
import numpy as np, itertools, sys
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot=tot+np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
def delv(W):   # deletion vector of the t-row matrix W at level t
    t=W.shape[0]
    if t==0: return np.ones(5)
    return np.array([sig(W,t,[c for c in range(5) if c!=j]) for j in range(5)])
def kernel_dims(w):
    out=[]
    for r,k in itertools.combinations(range(4),2):
        l,n=[i for i in range(4) if i not in (r,k)]; rows=[]
        for t in range(5):
            for T in itertools.combinations(range(4),t):
                Dv=delv(np.array([w[i] for i in T]).reshape(len(T),5))
                cv=np.concatenate([Dv, Dv*(l not in T), Dv*(n not in T)])
                rows.append(cv)
        A=np.array(rows); s=np.linalg.svd(A,compute_uv=False); out.append(15-int((s>1e-9*s[0]).sum()))
    return out
w=np.array([[1,-1,0,0,0],[0,0,1,-1,0],[1,1,-1,-1,0],[1,1,1,1,-4]],float)
print('orthogonal basis example: kernel dims per pair (r,k):',kernel_dims(w))
z=np.exp(2j*np.pi/5); m=np.array([z**j for j in range(5)])
print('Fourier (all parallel):',kernel_dims(np.array([m,m,m,m])))
