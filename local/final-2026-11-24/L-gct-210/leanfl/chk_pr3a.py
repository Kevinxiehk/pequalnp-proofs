import sympy as sp, itertools
v=sp.symbols('v0:4'); a,b,c=sp.symbols('a b c')
def pc(z1,z2,z3,z4):
    return sum(z1[i]*z2[j]*z3[k]*z4[l] for i,j,k,l in itertools.permutations(range(4)))
col=lambda s:[1+s*v[i] for i in range(4)]
one=[1]*4
T=sum(v); P=sum(x*x for x in v); t3=sum(x**3 for x in v)
expr=pc(col(a),col(b),col(c),one)-24-2*a*b*c*t3
cert=(6*(a+b+c)+2*(a*b+a*c+b*c)*T+a*b*c*(T**2-3*P))*T-2*(a*b+a*c+b*c)*P
print(sp.expand(expr-cert))
