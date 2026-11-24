# exact product-type column-centred 3x5 level 4-space: W_a = W_b = span(e_0, chi') with chi' = (0,1,i,-1,-i)  (NOTES-ncol R3.5)
import sympy as sp, itertools
I=sp.I; w=sp.Rational(-1,2)+sp.sqrt(3)*I/2
n1=[1,w,w**2]; n2=[sp.Rational(1,3)*x for x in [1,w**2,w]]
e0=[1,0,0,0,0]; chi=[0,1,I,-1,-I]
x,y,s,t=sp.symbols('x y s t')
a=[x*e0[j]+y*chi[j] for j in range(5)]; b=[s*e0[j]+t*chi[j] for j in range(5)]
Y=[[sp.expand(n1[i]*a[j]+3*n2[i]*b[j]) for j in range(5)] for i in range(3)]
def per(M):
    n=len(M); return sp.expand(sum(sp.prod([M[i][p[i]] for i in range(n)]) for p in itertools.permutations(range(n))))
def Pk(M,k):
    p=len(M); q=len(M[0]); return sp.expand(sum(per([[M[r][c] for c in C] for r in R]) for R in itertools.combinations(range(p),k) for C in itertools.combinations(range(q),k)))
print('column sums:',[sp.simplify(sum(Y[i][j] for i in range(3))) for j in range(5)])
print('P1,P2,P3:',[sp.simplify(Pk(Y,k)) for k in (1,2,3)])
vecs=[]
for k in (2,3):
    v=[sp.expand(Pk([[Y[i][c] for c in range(5) if c!=j] for i in range(3)],k)) for j in range(5)]
    for mono in set().union(*[set(sp.Poly(vj,x,y,s,t).monoms()) for vj in v if vj!=0]):
        vecs.append([sp.Poly(vj,x,y,s,t).coeff_monomial(mono) if vj!=0 else 0 for vj in v])
print('defect dimension (exact):',sp.Matrix(vecs).rank(simplify=True))
