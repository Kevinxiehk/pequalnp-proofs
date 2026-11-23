import numpy as np, itertools, sys
n=5
B=np.load(sys.argv[1]).reshape(-1,25)
U,S,Vh=np.linalg.svd(B,full_matrices=False)
perms=list(itertools.permutations(range(n)))
def perm(A): return sum(np.prod([A[i,p[i]] for i in range(n)]) for p in perms)
for k in range(len(S)):
    v=Vh[k].reshape(n,n)
    vals=[abs(perm(np.ones((n,n))+c*v)-120) for c in (0.5,1.0,2.0)]
    print(k,'sv %.2e'%S[k],'|perm(J+c v)-120| for c=.5,1,2:',['%.2e'%x for x in vals])
