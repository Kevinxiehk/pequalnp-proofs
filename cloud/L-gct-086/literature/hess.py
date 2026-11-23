import itertools, numpy as np, math
def perm(A):
    n=A.shape[0]
    if n==0: return 1.0
    return sum(np.prod([A[i,s[i]] for i in range(n)]) for s in itertools.permutations(range(n)))
for d in range(3,7):
    S=np.ones((d,d)); S[d-1,d-1]=1-d
    print(d,"perm(Sigma)=",perm(S))
    idx=[(i,j) for i in range(d) for j in range(d)]
    H=np.zeros((d*d,d*d))
    for a,(i,j) in enumerate(idx):
        for b,(k,l) in enumerate(idx):
            if i!=k and j!=l:
                r=[x for x in range(d) if x not in (i,k)]; c=[x for x in range(d) if x not in (j,l)]
                H[a,b]=perm(S[np.ix_(r,c)])
    ev=np.linalg.eigvalsh(H)
    print(" rank",np.sum(abs(ev)>1e-8),"n+",np.sum(ev>1e-8),"n-",np.sum(ev<-1e-8),"(d-1)^2+1=",(d-1)**2+1)
