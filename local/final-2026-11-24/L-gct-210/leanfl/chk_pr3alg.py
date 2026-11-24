import sympy as sp
p0,p1,l1,m0,m1=sp.symbols('p0 p1 l1 m0 m1')
hQl = m0*l1*(-1-l1) + m1*1*(-1-l1) + (-m0-m1)*1*l1
hB = m0*(p1*(-1-l1)+l1*(-p0-p1)) + m1*(p0*(-1-l1)+1*(-p0-p1)) + (-m0-m1)*(p0*l1+1*p1)
det = m0*m1-(-m0-m1)**2
Qp = m0*p1*(-p0-p1)+m1*p0*(-p0-p1)+(-m0-m1)*p0*p1
R = l1*m0*p0+2*m0*p0+m0*p1+2*m1*p0
goal = det*Qp**2
comb = (det*p0**2*Qp + det*p0**2*(p0*l1-p1)*R + Qp*R**2)*hQl - sp.Rational(1,4)*R**2*hB*hB
print(sp.expand(goal-comb))
