import sympy as sp
m,a,N,uu,rsu,l2,l3,l4,c2,c3,c4,e2,e3,e4=sp.symbols('m a N uu rsu l2 l3 l4 c2 c3 c4 e2 e3 e4')
s=e2+e3+e4
A2=l2-c2*N; A3=l3-c3*N; A4=l4-c4*N
B=m-(2*a+(c2+c3+c4)*N); C=rsu-(2*uu+(c2+c3+c4)*a); e=uu-rsu
L2=l2-e2*m; L3=l3-e3*m; L4=l4-e4*m
print('R1',sp.expand(((1-s)*m-2*a)-(B-A2-A3-A4+L2+L3+L4)))
print('R2',sp.expand((N*uu+s*m*a)-((-N)*e-N*C+a*A2+a*A3+a*A4-a*L2-a*L3-a*L4)))
R1=(1-s)*m-2*a; R2=N*uu+s*m*a; hs1=s-1
print('ha',sp.expand(a-(sp.Rational(-1,2)*R1-sp.Rational(1,2)*m*hs1)))
print('huu',sp.expand(N*uu-(R2-s*m*a)))
# Y0 with u=n: a=N, uu=N
R1n=(1-s)*m-2*N; h=N+s*m
print('h1',sp.expand(N*h-(N*N+s*m*N)))
print("h'",sp.expand((1+s)*N-((1-s)*h-s*R1n)))
