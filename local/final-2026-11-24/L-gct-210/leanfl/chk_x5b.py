import sympy as sp
y0=sp.symbols('y0_0:4'); y1=sp.symbols('y1_0:4'); v=sp.symbols('v0:4')
ip=lambda a,b: sum(a[i]*b[i] for i in range(4))
hn0=ip([2*y0[i]-v[i] for i in range(4)],[2*y0[i]-v[i] for i in range(4)])-ip(v,v)
hn1=ip([2*y1[i]-v[i] for i in range(4)],[2*y1[i]-v[i] for i in range(4)])-ip(v,v)
h01=[y0[i]+y1[i] for i in range(4)]
g1=ip(y0,y0); c1=sp.Rational(1,8)*(hn0+hn1)-sp.Rational(1,2)*sum((y1[i]-y0[i]-v[i])*h01[i] for i in range(4))
g2=ip(y0,v); c2=sp.Rational(1,8)*(hn1-hn0)-sp.Rational(1,2)*sum((y1[i]-y0[i]-v[i])*h01[i] for i in range(4))
print(sp.expand(g1-c1), sp.expand(g2-c2))
# orthogonality: p = phi0 Y = y0'-y1' (s = y0'+y1'); e1: <p, 2y0 - v> = 0 ; e2: <-p, 2y1 - v> = 0
p=sp.symbols('p0:4')
e1=ip(p,[2*y0[i]-v[i] for i in range(4)]); e2=ip([-x for x in p],[2*y1[i]-v[i] for i in range(4)])
# <p,y0> = (e1+e2)/4 + correction with h01 ; <p,v> = (e2 - e1)/... 
G1=ip(p,y0); C1=sp.Rational(1,4)*(e1+e2)+sp.Rational(1,2)*sum(p[i]*h01[i] for i in range(4))
G2=ip(p,v); C2=sp.Rational(1,2)*(e2-e1)+sum(p[i]*h01[i] for i in range(4))
print(sp.expand(G1-C1), sp.expand(G2-C2))
