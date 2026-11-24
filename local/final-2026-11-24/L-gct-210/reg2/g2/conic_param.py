# round 10: rational parametrisation over Q(w) of the conic 3m3^2-2m3m4+3m4^2-2m3-2m4+3 = 0 (the (2,2|2) conic double deformation)
# point P0 = ((1-w)/3, -w);  m = P0 + lam (1, s),  lam = -L(s)/Qd(s);  output D = 3 Qd, M3 = D m3, M4 = D m4 (polynomials in s, w), reduced mod w^2+w+1
import sympy as sp
s,w,l=sp.symbols('s w lam')
Q=lambda a,b: 3*a**2-2*a*b+3*b**2-2*a-2*b+3
red=lambda e: sp.expand(sp.rem(sp.expand(e),w**2+w+1,w))
P3,P4=(1-w)/3,-w
print('Q(P0) =',red(Q(P3,P4)))
e=sp.expand(Q(P3+l,P4+s*l)); Qd=sp.expand(e.coeff(l,2)); L=red(e.coeff(l,1))
print('Qd =',Qd,'  L =',L)
D=3*Qd; M3=red(sp.expand(P3*D-3*L)); M4=red(sp.expand(P4*D-3*s*L))
print('D =',D); print('M3 =',M3); print('M4 =',M4)
print('check Q(M3/D,M4/D)*D^2 =',red(sp.expand(3*M3**2-2*M3*M4+3*M4**2-2*M3*D-2*M4*D+3*D**2)))
open('conic.txt','w').write('%s;%s;%s'%(D,M3,M4))
