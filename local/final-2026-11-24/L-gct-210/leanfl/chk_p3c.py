import sympy as sp
v=sp.symbols('v0:4'); w=sp.symbols('w0:4')
ip=lambda a,b:sum(p*q for p,q in zip(a,b))
t3=lambda a,b,c:sum(a[i]*b[i]*c[i] for i in range(4))
t4=lambda a,b,c,d:sum(a[i]*b[i]*c[i]*d[i] for i in range(4))
sm=lambda l,a:[l*x for x in a]
def cubN(a,b,c): return t3(a,a,b)+t3(a,a,c)+t3(b,b,a)+t3(b,b,c)+t3(c,c,a)+t3(c,c,b)+t3(a,b,c)
def quaN(a,b,c): return 3*(t4(a,a,b,c)+t4(b,b,a,c)+t4(c,c,a,b))-(ip(a,b)*ip(a,c)+ip(b,a)*ip(b,c)+ip(c,a)*ip(c,b))
R=sp.Rational
# quart_two
e1=quaN(sm(1,v),sm(1,v),sm(1,w)); e2=quaN(sm(1,v),sm(1,v),sm(2,w)); hvv=ip(v,v)
goal=3*t4(v,v,w,w)-ip(v,w)**2
X=sp.Symbol('X')
# find coefficient X*hvv with X polynomial: goal - (1/2 e2 - e1) should be multiple of hvv
r=sp.expand(goal-(R(1,2)*e2-e1)); q,rem=sp.div(sp.Poly(r,*v,*w),sp.Poly(hvv,*v,*w))
print('quart_two remainder',rem.as_expr(),' coeff',q.as_expr())
# cub_two
c1=cubN(sm(1,v),sm(1,v),sm(0,w)); c2=cubN(sm(1,v),sm(0,v),sm(1,w)); c3=cubN(sm(1,v),sm(0,v),sm(2,w))
print('t3vvv',sp.expand(t3(v,v,v)-R(1,2)*c1))
print('t3vvw',sp.expand(t3(v,v,w)-(2*c2-R(1,2)*c3)))
print('t3vww',sp.expand(t3(v,w,w)-(R(1,2)*c3-c2)))
# three_rels
q1=quaN(v,v,v); r=sp.expand(t4(v,v,v,v)-R(1,9)*q1); q,rem=sp.div(sp.Poly(r,*v),sp.Poly(hvv,*v)); print('t4vvvv rem',rem.as_expr(),'coeff',q.as_expr())
