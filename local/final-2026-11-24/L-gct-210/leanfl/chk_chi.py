import sympy as sp
n=sp.symbols('n0:4')
p1=sum(n); p2=sum(x*x for x in n); p3=sum(x*x*x for x in n)
for i in range(4):
    x=n[i]
    A=x**3-p1*x**2/2+p1**2*x/6-p2*x/2
    B=x**2/2
    C=x/3
    print(i, sp.expand(x**4+n[0]*n[1]*n[2]*n[3]-(A*p1+B*p2+C*p3)))
