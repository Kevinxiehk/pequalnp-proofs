import sympy as sp
m0,m1,m2,kap,beta,b,s,t,p0,p1,p2=sp.symbols('m0 m1 m2 kap beta b s t p0 p1 p2')
A=[m0/4,m1/4,m2/4]; L=[p0+b*1,p1+b*s,p2+b*t]; B=[beta*m0,beta*m1,beta*m2]
A0,A1,A2=A; L0,L1,L2=L; B0,B1,B2=B
RHS = (24 + 6*(4*A0+4*A1+4*A2) + (2*(4*A0*(4*A1)+4*A0*(4*A2)+4*A1*(4*A2)) - 2*(4*(A0*A1+kap*(B0*B1))+4*(A0*A2+kap*(B0*B2))+4*(A1*A2+kap*(B1*B2))))
  + (4*A0*(4*A1)*(4*A2) - 4*A0*(4*(A1*A2+kap*(B1*B2))) - 4*A1*(4*(A0*A2+kap*(B0*B2))) - 4*A2*(4*(A0*A1+kap*(B0*B1)))
  + 2*(4*(A0*A1*A2+kap*(B0*B1*A2+B0*A1*B2+A0*B1*B2+B0*L1*L2+L0*B1*L2+L0*L1*B2)))))
goal = 8*kap*beta*(m0*((p1+b*s)*(p2+b*t))+m1*((p0+b*1)*(p2+b*t))+m2*((p0+b*1)*(p1+b*s))) - sp.Rational(3,4)*(m0*m1*m2)
F = sp.expand(goal - (RHS-24))
hb = 16*kap*beta**2-3
hm = m0+m1+m2
# F = cb*hb + cm*hm ; find cb by reducing
G = sp.groebner([hb,hm], m2, beta, kap, order='lex')
q, r = sp.reduced(F, [hm, hb], m2, beta, kap, m0, m1, b, s, t, p0, p1, p2, order='lex')
print('remainder', sp.simplify(r))
print('cm =', sp.factor(q[0])); print('cb =', sp.factor(q[1]))
print('check', sp.expand(F - q[0]*hm - q[1]*hb))
