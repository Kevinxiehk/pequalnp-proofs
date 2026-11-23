# Test the "initial term" (Groebner degeneration) criterion on the full DC space:
# DC space = cycle space of K_{n,n}; coordinate matroid = cographic; min-weight basis F(w) =
# complement of a max-weight spanning tree. Criterion for level: max-w k-matching not inside F(w).
import numpy as np, itertools
rng=np.random.default_rng(0)
def maxspan(n,w):
    edges=sorted(((w[i,j],i,j) for i in range(n) for j in range(n)),reverse=True)
    par=list(range(2*n))
    def f(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    T=set()
    for _,i,j in edges:
        a,b=f(i),f(n+j)
        if a!=b: par[a]=b; T.add((i,j))
    return T
def maxmatch(n,w,k):
    best=None
    for R in itertools.combinations(range(n),k):
        for C in itertools.permutations(range(n),k):
            s=sum(w[R[m],C[m]] for m in range(k))
            if best is None or s>best[0]: best=(s,[(R[m],C[m]) for m in range(k)])
    return best[1]
for n in (3,4,5):
    hits={k:0 for k in range(1,n+1)}
    for trial in range(300):
        w=rng.normal(size=(n,n))
        T=maxspan(n,w)
        for k in range(1,n+1):
            M=maxmatch(n,w,k)
            if all(e not in T for e in M): hits[k]+=1
    print(n,hits)
