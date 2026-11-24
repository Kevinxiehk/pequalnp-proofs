import sympy as sp, itertools
src=open('fam1111_mine.py').read().split("A=A.applyfunc(sp.expand)")[0]; exec(src)
def sig2(v):
    D=sp.Matrix(5,5,list(v)); return sum(D[i1,j1]*D[i2,j2] for (i1,i2) in itertools.combinations(range(5),2) for j1 in range(5) for j2 in range(5) if j1!=j2)
def bound(Am):
    T=Am.nullspace(); n=len(T); Q=sp.Matrix(n,n,lambda i,j: sp.expand((sig2(T[i]+T[j])-sig2(T[i])-sig2(T[j]))/2)); rk=Q.rank()
    return n,rk,(n-rk)+rk//2,[sum(v) for v in T].count(0)
A=A.applyfunc(sp.expand)
for av in (0,-2): print('a =',av,': (dim T_1, sigma_2 rank, isotropic bound, #basis with sigma_1 = 0) =',bound(A.subs(a,av)))
_,Ai=system(gens([0,0,-1,0,1],[0,0,-1,2,-1])); print('a = inf:',bound(Ai))
