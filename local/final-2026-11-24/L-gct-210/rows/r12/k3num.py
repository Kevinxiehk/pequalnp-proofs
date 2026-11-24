# numerical census of 3-dim strongly level spaces supported on exactly 3 columns (rows, round 12).
# K = rowspace of a 3x9 matrix (columns a, b, c in Walsh coordinates, dot form); conditions: <y_a,y_b>, <y_a,y_c>, <y_b,y_c> polarized = 0,
# t(y_a,y_b,y_c) polarized = 0 (t = 4 sym(x1 y2 z3)).  Records column ranks, row-sum rank q, d = dim(K cap {row sums 0}).
import numpy as np, itertools, sys
from scipy.optimize import least_squares
rng=np.random.default_rng(int(sys.argv[1])); NST=int(sys.argv[2])
def t(x,y,z): return sum(x[p[0]]*y[p[1]]*z[p[2]] for p in itertools.permutations(range(3)))
def res(B):  # B: 3 x 9 complex
    A=[B[:,0:3],B[:,3:6],B[:,6:9]]; r=[]
    for (j,l) in ((0,1),(0,2),(1,2)):
        G=A[j]@A[l].T; S=G+G.T; r+= [S[i,k] for i in range(3) for k in range(i,3)]
    for (i,j,k) in itertools.combinations_with_replacement(range(3),3):
        s=0
        for (p,q,w) in set(itertools.permutations((i,j,k))): s+=t(A[0][p],A[1][q],A[2][w])
        r.append(s)
    return np.array(r)
out=[]
for st in range(NST):
    piv=rng.choice(9,3,replace=False); free=[c for c in range(9) if c not in piv]
    def build(x):
        X=(x[:18]+1j*x[18:]).reshape(3,6); B=np.zeros((3,9),complex); B[:,piv]=np.eye(3); B[:,free]=X; return B
    f=lambda x: (lambda r: np.r_[r.real,r.imag])(res(build(x)))
    sol=least_squares(f,rng.normal(size=36),xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=4000)
    B=build(sol.x); nr=np.linalg.norm(res(B))
    if nr>1e-9: continue
    A=[B[:,0:3],B[:,3:6],B[:,6:9]]
    rk=[np.linalg.matrix_rank(a,1e-6) for a in A]
    RS=A[0]+A[1]+A[2]; q=np.linalg.matrix_rank(RS,1e-6)
    # Jacobian rank -> local dimension of the solution variety (in the chart)
    eps=1e-7; J=np.array([(f(sol.x+eps*e)-f(sol.x-eps*e))/(2*eps) for e in np.eye(36)]).T
    ldim=(36-np.linalg.matrix_rank(J,1e-5))//2
    out.append((tuple(sorted(rk)),q,3-q,ldim))
    print('start %d: col ranks %s  q %d  d %d  local dim %d'%(st,rk,q,3-q,ldim),flush=True)
from collections import Counter
print(Counter(out))
