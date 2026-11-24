# verify2 r16: exact check of reg2 R11-2: M111 (4x5 in rows 0-3 of a 5x5, row 4 = 0): level, dim 6, dim T_1, sigma_2-isotropic bound.
import sympy as sp, itertools
P=sp.symbols('p0:6')
def row(i,v): M=sp.zeros(5,5); M[i,:]=sp.Matrix([v]); return M
def col(m,v): M=sp.zeros(5,5); M[:4,m]=sp.Matrix(v); return M
G=[row(0,[0,0,0,1,-1]),row(1,[0,0,-2,1,1]),row(2,[0,-3,1,1,1]),col(0,[1,1,-3,1]),col(1,[1,-2,0,1]),col(2,[1,0,0,-1])]
Y=sum((P[k]*G[k] for k in range(6)),sp.zeros(5,5)); M=sp.ones(5,5)+Y
def perm(A):
    n=A.shape[0]; return sp.expand(sum(sp.prod([A[i,f[i]] for i in range(n)]) for f in itertools.permutations(range(n))))
print('perm(J+Y) =',perm(M),'(level iff 120)')
print('dim M111 =',sp.Matrix([list(g) for g in G]).rank())
cof={(i,j):perm(M.extract([k for k in range(5) if k!=i],[l for l in range(5) if l!=j])) for i in range(5) for j in range(5)}
mons=set()
for e in cof.values(): mons|=set(sp.Poly(e,*P).monoms())
idx=[(i,j) for i in range(5) for j in range(5)]
A=sp.Matrix([[sp.Poly(cof[k],*P).coeff_monomial(m) for k in idx] for m in sorted(mons)])
T=A.nullspace(); n=len(T); print('dim T_1(M111) =',n)
s1=sp.Matrix([[sum(v) for v in T]]); T1s=[sum((w[k]*T[k] for k in range(n)),sp.zeros(25,1)) for w in s1.nullspace()]
def sig2(v):
    D=sp.Matrix(5,5,list(v)); return sum(D[i1,j1]*D[i2,j2] for (i1,i2) in itertools.combinations(range(5),2) for j1 in range(5) for j2 in range(5) if j1!=j2)
m=len(T1s); Q=sp.Matrix(m,m,lambda i,j: sp.expand((sig2(T1s[i]+T1s[j])-sig2(T1s[i])-sig2(T1s[j]))/2)); rk=Q.rank()
print('dim T_1 cap {sigma_1=0} =',m,' sigma_2 rank',rk,' => level L containing M111 has dim <=',(m-rk)+rk//2)
