# Round 15: hand proof of the PARALLEL case of Lemma S2 via the rank-2 permanent expansion.
# Y = a (x) m' + b (x) g, m' = (1,1,1,1,-2), g = (0,0,1,be,-1-be).  perm(J + t(a m^T + b g^T)) (4x4) =
#   sum_{k2,k3} t^{k2+k3} (4-k2-k3)! k2! k3! E_{k2,k3}(a,b) E_{k2,k3}(m,g),   E_{k2,k3}(x,y) = sum_{R2, R3 disjoint, |R2|=k2, |R3|=k3} prod_R2 x prod_R3 y.
# Defect in C m0  <=>  W . (D_j)_j = 0, W = basis of m0^perp. Degree d: N_d(be) x = 0, x = (E_{k2,k3}(a,b))_{k2+k3=d}.
import sympy as sp, itertools
be=sp.Symbol('be')
def E(k2,k3,x,y):
    n=len(x); tot=0
    for R2 in itertools.combinations(range(n),k2):
        rest=[r for r in range(n) if r not in R2]
        for R3 in itertools.combinations(rest,k3):
            tot+=sp.prod([x[r] for r in R2])*sp.prod([y[r] for r in R3])
    return sp.expand(tot)
m=[1,1,1,1,-2]; g=[0,0,1,be,-1-be]
W=sp.Matrix([[1,-1,0,0,0],[0,1,-1,0,0],[0,0,1,-1,0],[0,0,0,4,1]])
for d in (2,3,4):
    ks=[(k2,d-k2) for k2 in range(d,-1,-1)]
    M=sp.Matrix(5,len(ks),lambda j,c: sp.factorial(4-d)*sp.factorial(ks[c][0])*sp.factorial(ks[c][1])*E(ks[c][0],ks[c][1],[m[x] for x in range(5) if x!=j],[g[x] for x in range(5) if x!=j]))
    N=sp.simplify(W*M)
    print('degree',d,'columns (k2,k3) =',ks); sp.pprint(N.applyfunc(sp.factor))
    if N.shape[0]==N.shape[1]: print('  det =',sp.factor(N.det()))
    else:
        mins=[sp.factor(N.extract(list(rows),list(range(N.shape[1]))).det()) for rows in itertools.combinations(range(4),N.shape[1])]
        print('  maximal minors:',mins)
