import numpy as np, itertools, math
def perm(M):
    n=M.shape[0]; return sum(np.prod([M[i,s[i]] for i in range(n)]) for s in itertools.permutations(range(n)))
rng=np.random.default_rng(1)
# CC formula check for 4x4 column-centred: P2=-sum e2(rows), P3=2 sum e3(rows)
def Pk(Z,k):
    n,m=Z.shape; tot=0
    for R in itertools.combinations(range(n),k):
        for C in itertools.combinations(range(m),k):
            tot+=perm(Z[np.ix_(R,C)])
    return tot
def e(v,k): return sum(np.prod(c) for c in itertools.combinations(v,k))
Z=rng.normal(size=(4,4))+1j*rng.normal(size=(4,4)); Z-=Z.mean(0)
print(abs(Pk(Z,2)+sum(e(z,2) for z in Z)), abs(Pk(Z,3)-2*sum(e(z,3) for z in Z)))
# e3(v minus d) formula
v=rng.normal(size=5); v-=v.mean(); d=v[2]; w=np.delete(v,2)
print(abs(e(w,3)-( (v**3).sum()/3 - d**3 + d*(v**2).sum()/2)))
# perm[v,v,v',v'] with v=chi3, v'=chi1
I=1j; chi=lambda a: np.array([I**(a*j) for j in range(4)])
M=np.column_stack([chi(3),chi(3),chi(1),chi(1)]); print('perm[v,v,vp,vp]=',perm(M))
print('perm[v,vp,vp,vp]=',perm(np.column_stack([chi(3),chi(1),chi(1),chi(1)])))
