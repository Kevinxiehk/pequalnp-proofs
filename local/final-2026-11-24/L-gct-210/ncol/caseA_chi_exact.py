# exact: defect dimension of L' = {(a chi^T | x) : a in C^{012}, x in 1^perp}, chi = (1,i,-1,-i), over Q(i)
import sympy as sp, itertools, random
I=sp.I; chi=[1,I,-1,-I]
def per(M):
    n=len(M); return sp.expand(sum(sp.prod([M[i][p[i]] for i in range(n)]) for p in itertools.permutations(range(n))))
random.seed(3); vecs=[]
for t in range(6):
    a=[random.randint(-5,5) for _ in range(3)]+[0]; x=[random.randint(-5,5) for _ in range(3)]; x.append(-sum(x))
    Y=[[a[i]*chi[j] for j in range(4)]+[x[i]] for i in range(4)]
    c=[per([[1+Y[i][k] for k in range(5) if k!=j] for i in range(4)])-24 for j in range(5)]
    vecs.append(c)
M=sp.Matrix(vecs); print('sum of each defect vector:',[sp.simplify(sum(v)) for v in vecs]); print('exact rank =',M.rank(simplify=True))
