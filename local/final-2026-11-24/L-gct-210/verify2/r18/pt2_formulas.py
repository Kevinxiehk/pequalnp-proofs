# verify2 r18: check ncol's product-type formulas from first principles. 3x5 column-centred Y with rows y_k = a w^k + b w^{2k} (k = 0,1,2), w^2+w+1 = 0
# ("isotropic coordinates"). Compute P_m = sigma_m(Y) and the deletion vectors D_m(Y)_j = sigma_m(Y minus column j); compare with
# P_2 ~ a.b - A B, P_3 ~ e_3(a) + e_3(b), d2 ~ A b + B a - 2 a o b, d3 ~ d3a(a) + d3b(b), d3a_j = -a_j (e_2(a) - A a_j + a_j^2) (on e_3(a) = 0).
import sympy as sp, itertools
w=sp.Symbol('w'); a=sp.symbols('a0:5'); b=sp.symbols('b0:5')
Y=sp.Matrix([[a[j]*w**k+b[j]*w**(2*k) for j in range(5)] for k in range(3)])
def red(e): return sp.expand(sp.rem(sp.expand(e),w**2+w+1,w))
def sig(M,m,cols): return red(sum(sp.prod([M[R[i],C[i]] for i in range(m)]) for R in itertools.combinations(range(3),m) for C in itertools.permutations(cols,m)))
A,B=sum(a),sum(b); dot=sum(x*y for x,y in zip(a,b))
e2=lambda v: sum(v[i]*v[j] for i,j in itertools.combinations(range(5),2)); e3=lambda v: sum(v[i]*v[j]*v[k] for i,j,k in itertools.combinations(range(5),3))
P2=sig(Y,2,range(5)); P3=sig(Y,3,range(5))
print('P_2 / (a.b - A B) =',sp.simplify(P2/(dot-A*B)),'   P_3 / (e3(a)+e3(b)) =',sp.simplify(P3/(e3(a)+e3(b))))
D2=[sig(Y,2,[q for q in range(5) if q!=j]) for j in range(5)]; D3=[sig(Y,3,[q for q in range(5) if q!=j]) for j in range(5)]
d2=[A*b[j]+B*a[j]-2*a[j]*b[j] for j in range(5)]
print('D_2 / d2 per column:',[sp.simplify(D2[j]/d2[j]) for j in range(5)])
# D_3: compare modulo the level relations (e3(a) = 0 = e3(b), a.b = A B) -- test general form first
d3a=lambda v,j: -v[j]*(e2(v)-sum(v)*v[j]+v[j]**2)
diff=[sp.expand(D3[j]-sp.Symbol('c')*(d3a(a,j)+d3a(b,j))) for j in range(5)]
# find c from a monomial and test remainder modulo e3(a), e3(b)
c=sp.Symbol('c')
for cv in (1,-1,3,-3,sp.Rational(3,2),-sp.Rational(3,2),6,-6):
    ok=True
    for j in range(5):
        r=sp.expand(D3[j]-cv*(d3a(a,j)+d3a(b,j)))
        # reduce modulo e3(a) and e3(b): r must be a combination  alpha_j * e3(a) + beta_j * e3(b) with alpha, beta of degree 0 in a/b resp.
        Ra=sp.Poly(r,*a); Rb=sp.Poly(r,*b)
        q=sp.symbols('q0:2')
        cand=sp.expand(r-q[0]*e3(a)-q[1]*e3(b))
        sol=sp.solve(sp.Poly(cand,*a,*b).coeffs(),q,dict=True)
        if not sol: ok=False; break
    if ok: print('D_3 = %s * (d3a(a) + d3a(b)) + (const) * e3(a) + (const) * e3(b)  per column'%cv); break
else: print('D_3 not of the stated form with small constants; D3[0] =',sp.factor(D3[0])[:200] if False else 'see log')
