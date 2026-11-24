import sympy as sp, itertools
d=sp.symbols('d0:4'); z=sp.symbols('z0:4'); a=sp.symbols('a0:4'); b=sp.symbols('b0:4'); w=sp.symbols('w0:4')
c,t=sp.symbols('c t')
def pc(z1,z2,z3,z4): return sum(z1[i]*z2[j]*z3[k]*z4[l] for i,j,k,l in itertools.permutations(range(4)))
tau=lambda v: sum(v); ip=lambda x,y: sum(x[i]*y[i] for i in range(4))
e2=lambda v: (tau(v)**2-ip(v,v))/2
e2b=lambda x,y: (tau(x)*tau(y)-ip(x,y))/2
Ed=lambda v: [e2(v)-tau(v)*v[k]+v[k]**2 for k in range(4)]
Edb=lambda x,y: [e2b(x,y)-(tau(x)*y[k]+tau(y)*x[k])/2+x[k]*y[k] for k in range(4)]
lhs=pc([c*d[k]+t*z[k] for k in range(4)],[c*d[k]+t*z[k] for k in range(4)],[1+c*a[k] for k in range(4)],[1+c*b[k] for k in range(4)]) - pc([c*d[k] for k in range(4)],[c*d[k] for k in range(4)],[1+c*a[k] for k in range(4)],[1+c*b[k] for k in range(4)])
apb=[a[k]+b[k] for k in range(4)]
rhs=2*t*c*(4*e2b(d,z)+2*c*ip(apb,Edb(d,z))+c**2*pc(d,z,a,b)) + t**2*(4*e2(z)+2*c*ip(apb,Ed(z))+c**2*pc(z,z,a,b))
print('pc_F_expand', sp.expand(lhs-rhs))
# polarisation identities
zw=[z[k]+w[k] for k in range(4)]
print('Ed_pol', [sp.expand(Ed(zw)[k]-Ed(z)[k]-Ed(w)[k]-2*Edb(z,w)[k]) for k in range(4)])
print('pc_pol', sp.expand(pc(zw,zw,a,b)-pc(z,z,a,b)-pc(w,w,a,b)-2*pc(z,w,a,b)))
