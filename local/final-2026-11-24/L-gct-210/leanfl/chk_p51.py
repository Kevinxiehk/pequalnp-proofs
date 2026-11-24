import sympy as sp, itertools
a=sp.symbols('a0:4'); x=sp.symbols('x0:4'); al,be,ga=sp.symbols('al be ga')
def pc(z1,z2,z3,z4): return sum(z1[i]*z2[j]*z3[k]*z4[l] for i,j,k,l in itertools.permutations(range(4)))
tau=lambda v: sum(v); ip=lambda u,v: sum(u[i]*v[i] for i in range(4)); t3=lambda u: sum(e**3 for e in u)
e2=lambda v: (tau(v)**2-ip(v,v))/2
e3v=lambda v: (tau(v)**3-3*tau(v)*ip(v,v)+2*t3(v))/6
E2v=[e2(a)-a[i]*(tau(a)-a[i]) for i in range(4)]
E3v=[e3v(a)-a[i]*E2v[i] for i in range(4)]
# check E2v, E3v are e2/e3 of a without i
for i in range(4):
    rest=[a[k] for k in range(4) if k!=i]
    assert sp.expand(E2v[i]-(rest[0]*rest[1]+rest[0]*rest[2]+rest[1]*rest[2]))==0
    assert sp.expand(E3v[i]-rest[0]*rest[1]*rest[2])==0
lhs=pc([1+al*e for e in a],[1+be*e for e in a],[1+ga*e for e in a],list(x))
rhs=6*tau(x)+(al+be+ga)*(2*(tau(x)*tau(a)-ip(x,a)))+(al*be+al*ga+be*ga)*(2*ip(x,E2v))+al*be*ga*(6*ip(x,E3v))
print('pc_x4', sp.expand(lhs-rhs))
# conversion to c-form
m=sp.symbols('m0:5'); th,u1,u2,u3,tx=sp.symbols('th u1 u2 u3 tx')
E2=sum(m[i]*m[j] for i,j in itertools.combinations(range(4),2)); E3=sum(m[i]*m[j]*m[k] for i,j,k in itertools.combinations(range(4),3))
hm=sum(m)
c3=-u3; c2=u2-m[4]*u3; c1=-u1+m[4]*u2-E2*u3-th; c0=-m[4]*u1+E2*u2+E3*u3+6*tx
mult={}
for j in range(4):
    o=[m[k] for k in range(4) if k!=j]
    eq=6*tx+(o[0]+o[1]+o[2])*u1+(o[0]*o[1]+o[0]*o[2]+o[1]*o[2])*u2+o[0]*o[1]*o[2]*u3-th*m[j]
    target=c0+c1*m[j]+c2*m[j]**2+c3*m[j]**3
    q,r=sp.div(sp.expand(target-eq), hm, m[4])
    print('j',j,'rem',sp.simplify(r),'mult',sp.factor(q))
# cubic4 certificate
y=sp.symbols('y0:4'); cc=sp.symbols('c0:4')
P=lambda t: cc[0]+cc[1]*t+cc[2]*t**2+cc[3]*t**3
V=sp.prod([y[k]-y[i] for i in range(4) for k in range(i+1,4)])
coef=[sp.factor(sp.cancel(V/sp.prod([y[k]-y[l] for l in range(4) if l!=k]))) for k in range(4)]
print('cubic coefs', coef)
print('cert3', sp.expand(sum(coef[k]*P(y[k]) for k in range(4)) - cc[3]*V))
V3=sp.prod([y[k]-y[i] for i in range(3) for k in range(i+1,3)])
coef3=[sp.factor(sp.cancel(V3/sp.prod([y[k]-y[l] for l in range(3) if l!=k]))) for k in range(3)]
P2=lambda t: cc[0]+cc[1]*t+cc[2]*t**2
print('quad coefs', coef3, sp.expand(sum(coef3[k]*P2(y[k]) for k in range(3)) - cc[2]*V3))
