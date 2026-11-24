import sympy as sp
m=sp.symbols('m0:5'); ipfx=sp.symbols('ipfx'); a=sp.symbols('a0:5')  # a_j = ip(g_j, x)
R = sum(m[j]*a[j] for j in range(5)); hm=sum(m)
for n in range(5):
    E=[(a[j]-ipfx) if j==n else (-a[j]-ipfx) for j in range(5)]
    comb = sp.Rational(1,2)*(R - m[n]*E[n] + sum(m[j]*E[j] for j in range(5) if j!=n) + ipfx*hm)
    print(n, sp.expand(m[n]*ipfx - comb))
