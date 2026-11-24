# Round 17: EXPLICIT X violating (PR3) as stated (rows in 2-planes = row projections of dim <= 2): exact rational check with fractions.
# X = span{x_b, x_c, x_d}, rho = 1 (any rho not in {0,-1}):
#   x_b = [[-1,0,0,0,0],[1,1,-1,0,0],[0,0,0,0,0]],  x_c = [[-1,0,0,0,0],[0,0,0,0,0],[1,0,0,1,-1]],  x_d = [[1,0,0,0,0],[rho,0,0,0,0],[-1-rho,0,0,0,0]].
# N = X (+) e_3 (x) Z, Z = {z : sum z = 0, z_1 = z_2, z_3 = z_4} (2-dim): a 5-dim 4x5 space. Checks (exact, sympy): sigma_1..3 of X and sigma_1..4 of N
# vanish identically; deletion vectors of X span 2 dims; single-row parts; row projections.
import sympy as sp, itertools
rho=sp.Integer(1)
xb=sp.Matrix([[-1,0,0,0,0],[1,1,-1,0,0],[0,0,0,0,0]]); xc=sp.Matrix([[-1,0,0,0,0],[0,0,0,0,0],[1,0,0,1,-1]]); xd=sp.Matrix([[1,0,0,0,0],[rho,0,0,0,0],[-1-rho,0,0,0,0]])
b,c,d,z1,z2=sp.symbols('b c d z1 z2')
X=b*xb+c*xc+d*xd
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot+=sp.prod([M[R[k],C[k]] for k in range(m)])
    return sp.expand(tot)
print('X level:',[sig(X,m,range(5)) for m in (1,2,3)])
D=[[sig(X,m,[q for q in range(5) if q!=j]) for j in range(5)] for m in (1,2,3)]
vecs=[]
for m in range(3):
    P=sp.Poly(sum(D[m][j]*sp.Symbol('e%d'%j) for j in range(5)),b,c,d)
    for cf in P.coeffs(): vecs.append([sp.expand(cf).coeff(sp.Symbol('e%d'%j)) for j in range(5)])
print('deletion vectors: rank',sp.Matrix(vecs).rank(),' (defect of X)')
zv=[ -2*z1-2*z2, z1, z1, z2, z2]
Nm=X.col_join(sp.Matrix([zv]))
print('N = X + e_3 Z level:',[sig(Nm,m,range(5)) for m in (1,2,3,4)])
# single-row elements of X / row projections
for r in range(3):
    others=[i for i in range(3) if i!=r]
    eqs=[X[i,j] for i in others for j in range(5)]
    sol=sp.solve(eqs,[b,c,d],dict=True)
    print('row',r,': elements with the other rows zero:',sol,'; row projection dim',sp.Matrix([[sp.diff(X[r,j],v) for j in range(5)] for v in (b,c,d)]).rank())
