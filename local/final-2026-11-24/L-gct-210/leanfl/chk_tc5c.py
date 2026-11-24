import sympy as sp, itertools
d=sp.symbols('d0:4'); a=sp.symbols('a0:4'); b=sp.symbols('b0:4'); c=sp.symbols('c')
def pc(z1,z2,z3,z4): return sum(z1[i]*z2[j]*z3[k]*z4[l] for i,j,k,l in itertools.permutations(range(4)))
tau=lambda v: sum(v); ip=lambda x,y: sum(x[i]*y[i] for i in range(4))
e2=lambda v: (tau(v)**2-ip(v,v))/2
Ed=lambda v: [e2(v)-tau(v)*v[k]+v[k]**2 for k in range(4)]
lhs=pc([c*x for x in d],[c*x for x in d],[1+c*x for x in a],[1+c*x for x in b])
rhs=c**2*(4*e2(d)+2*c*ip([a[k]+b[k] for k in range(4)],Ed(d))+c**2*pc(d,d,a,b))
print('pc_dd_scale', sp.expand(lhs-rhs))
