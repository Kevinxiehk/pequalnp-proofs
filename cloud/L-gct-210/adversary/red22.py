import sympy as sp
Z11,Z12,Z21,Z22,s1,s2,c1,c2=sp.symbols('Z11 Z12 Z21 Z22 s1 s2 c1 c2')
R1=Z11+Z12;R2=Z21+Z22;K1=Z11+Z21;K2=Z12+Z22
F=(s1+s2)*(c1+c2)+s1*R2+s2*R1+Z11*Z22+Z12*Z21+c1*K2+c2*K1
E3=sp.expand(c1*(s1*Z22+s2*Z12)+c2*(s1*Z21+s2*Z11)-(c1+c2)*F)
E1=s1+s2+Z11+Z12+Z21+Z22+c1+c2
print('E3 =',sp.factor(E3))
E3r=sp.expand(E3.subs(Z22,sp.solve(E1,Z22)[0]))
print('E3 on E1:',sp.factor(E3r))
