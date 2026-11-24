import sympy as sp
m=sp.symbols('m0:5'); ka=sp.symbols('ka'); f=sp.symbols('f0:4')
G=[sp.symbols('g%d_0:4'%j) for j in range(5)]
ip=lambda a,b: sum(a[i]*b[i] for i in range(4))
i=0
row=sum(ka*m[j]/4+m[j]*G[j][i] for j in range(5)); hm=sum(m)
hg1=G[1][i]+G[0][i]; hg2=G[2][i]+f[i]; hg3=G[3][i]+f[i]; hg4=G[4][i]+f[i]
goal=(m[0]-m[1])*G[0][i]+(m[0]+m[1])*f[i]
comb=row-(ka/4)*hm-m[1]*hg1-m[2]*hg2-m[3]*hg3-m[4]*hg4+f[i]*hm
print('hrel2',sp.expand(goal-comb))
A=m[0]-m[1];B=m[0]+m[1]; g=G[0]
nu=ip(f,f); n0=ip(g,g)-nu
hrel=[A*g[k]+B*f[k] for k in range(4)]
goal=nu*m[0]*m[1]
comb=sp.Rational(1,4)*A**2*n0-sp.Rational(1,4)*sum((A*g[k]-B*f[k])*hrel[k] for k in range(4))
print('h4',sp.expand(goal-comb))
# one column: g0 = f, g_j=-f
hg=[G[j][i]+f[i] for j in range(1,5)]; hg0=G[0][i]-f[i]
goal=2*m[0]*f[i]
comb=row-(ka/4)*hm - m[0]*hg0 - sum(m[j]*hg[j-1] for j in range(1,5)) + f[i]*hm
print('hrel1',sp.expand(goal-comb))
