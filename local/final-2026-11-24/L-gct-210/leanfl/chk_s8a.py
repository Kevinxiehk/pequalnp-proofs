import sympy as sp
u=sp.symbols('u0:4'); y2=sp.symbols('p0:4'); y3=sp.symbols('q0:4'); y4=sp.symbols('r0:4'); v=sp.symbols('v0:4'); a,b=sp.symbols('a b')
tau=lambda x: sum(x)
ip=lambda x,y: sum(x[i]*y[i] for i in range(4))
def X2c(z1,z2,z3,z4):
    Z=[z1,z2,z3,z4]
    return 2*sum(tau(Z[i])*tau(Z[j]) for i in range(4) for j in range(i+1,4)) - 2*sum(ip(Z[i],Z[j]) for i in range(4) for j in range(i+1,4))
add=lambda x,y:[x[i]+y[i] for i in range(4)]; sm=lambda c,x:[c*xi for xi in x]
c=-(a+b)
e1=X2c(u,add(y2,sm(a,v)),add(y3,sm(b,v)),add(y4,sm(c,v)))
e2=X2c(u,y2,y3,y4)
G=a*(ip(v,y4)-ip(v,y2))+b*(ip(v,y4)-ip(v,y3))
D=sp.expand(e1-e2)
# find p,q with D = k*G + p*tau(v) + q*ip(v,v)
k=sp.Symbol('k')
tv=tau(v); iv=ip(v,v)
# guess: D = -2*G + (linear in tau v) + c2*iv
R=sp.expand(D+2*G)
print('R =',sp.factor(R))
tv=tau(v); iv=ip(v,v); s=a**2+a*b+b**2
cert=sp.expand((-2*s*tv - 2*(a*(tau(y2)-tau(y4))+b*(tau(y3)-tau(y4))))*tv + 2*s*iv - (e1-e2))
print('check 2G:', sp.expand(2*G - cert))
