# verify2 r16: EXACT T_1 and sigma_2-isotropic (FO2_0) bound for stage3's explicit member N (rows 0-3 of a 5x5, row 4 = 0).
# A level L (5x5) containing N: L c T_1(N) = {D : sum_ij D_ij perm(minor_ij(J+Y)) = 0 for all Y in N}, sigma_1(D) = sigma_2(D) = 0 on L.
import sympy as sp, itertools, sys
rv=sp.Rational(sys.argv[1]) if len(sys.argv)>1 else sp.Integer(1)
b,c,d,s,r=P=sp.symbols('b c d s r')
xb=sp.Matrix([[-1,0,0,0,0],[1,1,-1,0,0],[0,0,0,0,0]]); xc=sp.Matrix([[-1,0,0,0,0],[0,0,0,0,0],[1,0,0,1,-1]])
xd=sp.Matrix([[1,0,0,0,0],[rv,0,0,0,0],[-1-rv,0,0,0,0]])
Y=(b*xb+c*xc+d*xd).col_join(sp.Matrix([[-2*s-2*r,s,s,r,r]])).col_join(sp.zeros(1,5))
M=sp.ones(5,5)+Y
def perm(A):
    n=A.shape[0]; return sp.expand(sum(sp.prod([A[i,f[i]] for i in range(n)]) for f in itertools.permutations(range(n))))
cof={(i,j):perm(M.extract([k for k in range(5) if k!=i],[l for l in range(5) if l!=j])) for i in range(5) for j in range(5)}
mons=set()
for e in cof.values(): mons|=set(sp.Poly(e,*P).monoms())
mons=sorted(mons); idx=[(i,j) for i in range(5) for j in range(5)]
A=sp.Matrix([[sp.Poly(cof[k],*P).coeff_monomial(m) for k in idx] for m in mons])
T=A.nullspace(); n=len(T); print('rho =',rv,': dim T_1(N) =',n)
s1=sp.Matrix([[sum(v) for v in T]]); T1s=[sum((w[k]*T[k] for k in range(n)),sp.zeros(25,1)) for w in s1.nullspace()]
print('   dim T_1 cap {sigma_1 = 0} =',len(T1s))
def sig2(v):
    D=sp.Matrix(5,5,list(v)); return sum(D[i1,j1]*D[i2,j2] for (i1,i2) in itertools.combinations(range(5),2) for j1 in range(5) for j2 in range(5) if j1!=j2)
m=len(T1s); Q=sp.Matrix(m,m,lambda i,j: sp.expand((sig2(T1s[i]+T1s[j])-sig2(T1s[i])-sig2(T1s[j]))/2))
rk=Q.rank(); print('   sigma_2 form on it: rank',rk,' => max isotropic dim',(m-rk)+rk//2,'(bound for dim L)')
# also with sigma_1 not imposed (stage3's FO2_0 convention)
Q0=sp.Matrix(n,n,lambda i,j: sp.expand((sig2(T[i]+T[j])-sig2(T[i])-sig2(T[j]))/2)); rk0=Q0.rank(); print('   stage3 convention (no sigma_1): FO2_0 =',(n-rk0)+rk0//2)
