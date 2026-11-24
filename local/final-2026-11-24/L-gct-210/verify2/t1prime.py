import sympy as sp
a,b,c,c2,c3=sp.symbols('a b c c2 c3')
I=sp.I; y=(-1+I)/2
eqs=[a+b+c-1, c2*(I*a+b-c)-1, c3*(-a+b+I*c)-1, c+c2*b+y, a+c3*b+y, I*(c2*a+c3*c)+y]
G=sp.groebner(eqs,a,b,c,c2,c3,order='lex',domain=sp.QQ.algebraic_field(I))
print('Groebner basis of the cyclic Type II system:',G.exprs)
