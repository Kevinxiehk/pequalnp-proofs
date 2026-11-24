# verify2: (TV) ingredient: for a 2-plane P in C^5, K(P) = {Q in A_2 : Q V = 0 in A_3 for all v in P} has dim <= 1. Random + structured planes.
import numpy as np, itertools
rng=np.random.default_rng(2)
pairs=list(itertools.combinations(range(5),2)); trip=list(itertools.combinations(range(5),3)); pi={p:k for k,p in enumerate(pairs)}
def mulmat(v):
    M=np.zeros((10,10),complex)
    for a,t in enumerate(trip):
        for m in t:
            p=tuple(x for x in t if x!=m); M[a,pi[p]]+=v[m]
    return M
def dimK(v,w):
    A=np.vstack([mulmat(v),mulmat(w)]); s=np.linalg.svd(A,compute_uv=False); return 10-int(np.sum(s>1e-9*s[0]))
hist={}
for size in (2,3,4,5):
    for S in itertools.combinations(range(5),size):
        for rep in range(30):
            while True:
                v=np.zeros(5,complex); w=np.zeros(5,complex)
                # structured: random small integers incl. zeros inside the support, plus generic complex
                if rep%2==0:
                    v[list(S)]=rng.integers(-2,3,size=size); w[list(S)]=rng.integers(-2,3,size=size)
                else:
                    v[list(S)]=rng.normal(size=size)+1j*rng.normal(size=size); w[list(S)]=rng.normal(size=size)+1j*rng.normal(size=size)
                if np.linalg.matrix_rank(np.array([v,w]))==2 and all(abs(v[j])+abs(w[j])>0 for j in S): break
            k=(size,dimK(v,w)); hist[k]=hist.get(k,0)+1
print('(support size of P, dim K(P)) -> count:',dict(sorted(hist.items())))
