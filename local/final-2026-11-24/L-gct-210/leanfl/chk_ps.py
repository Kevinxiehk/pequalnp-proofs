import sympy as sp
z=sp.symbols('z0:4'); y=sp.symbols('y0:4'); s=sp.symbols('s0:4')
k1,k2,mj,th1,th2=sp.symbols('k1 k2 mj th1 th2')
ip=lambda a,b: sum(a[i]*b[i] for i in range(4))
add=lambda a,b:[a[i]+b[i] for i in range(4)]
sub=lambda a,b:[a[i]-b[i] for i in range(4)]
neg=lambda a:[-x for x in a]
tau=lambda a: sum(a)
# pol_alg
goal = ip(z,[2*y[i]-s[i] for i in range(4)]) - (-(th1-th2)/4)*mj
e1 = ip(add(z,y),add(z,y)) - ip(s,add(z,y)) - k1**2*mj**2 + (th1/2)*mj
e2 = ip(sub(z,y),sub(z,y)) - ip(neg(s),sub(z,y)) - k2**2*mj**2 + (th2/2)*mj
c1 = tau(add(z,y)) - k1*mj; c2 = tau(sub(z,y)) - k2*mj; ty = tau(y)
comb = sp.Rational(1,2)*(e1-e2) - sp.Rational(1,2)*(tau(add(z,y))+k1*mj)*c1 + sp.Rational(1,2)*(tau(sub(z,y))+k2*mj)*c2 + 2*tau(z)*ty
print('pol_alg', sp.expand(goal-comb))
# np3_col
g=sp.symbols('g0:4'); ka,kap,th,nu=sp.symbols('ka kap th nu')
zc=[ka*mj/4+mj*g[i] for i in range(4)]
goal = mj**2*(nu-3*ka**2/4) + (th/2)*mj
hb = ip(zc,zc) - 0 - kap**2*mj**2 + (th/2)*mj
hn = ip(g,g)-nu; ht=tau(g); hc=tau(zc)-kap*mj; hk=tau(zc)-ka*mj
T = ka*mj + mj*tau(g)
comb = hb - mj**2*hn - (ka*mj**2/2)*ht - (T+kap*mj)*hc + (T+ka*mj)*hk
print('np3_col', sp.expand(goal-comb))
# hrel
m=sp.symbols('m0:5'); G=[sp.symbols('g%d_0:4'%j) for j in range(5)]; f=sp.symbols('f0:4')
i=0
row = sum(ka*m[j]/4 + m[j]*G[j][i] for j in range(5))
hm = sum(m)
hg3 = G[3][i]+f[i]; hg4 = G[4][i]+f[i]; hsum = G[0][i]+G[1][i]+G[2][i]+f[i]
goal = (m[1]+m[2])*G[0][i]+(m[0]+m[2])*G[1][i]+(m[0]+m[1])*G[2][i]
comb = -row + (ka/4)*hm + m[3]*hg3 + m[4]*hg4 + (m[0]+m[1]+m[2])*hsum - f[i]*hm
print('hrel', sp.expand(goal-comb))
# E4
g0,g1,g2=[sp.symbols('a%d_0:4'%j) for j in range(3)]
nu_=ip(f,f)
goal = 3*nu_ + 2*(ip(g1,g2)+ip(g0,g2)+ip(g0,g1)) - nu_
comb = sum((g0[i]+g1[i]+g2[i]-f[i])*(g0[i]+g1[i]+g2[i]+f[i]) for i in range(4)) - (ip(g0,g0)-nu_) - (ip(g1,g1)-nu_) - (ip(g2,g2)-nu_)
print('E4', sp.expand(goal-comb))
# h8
al,be,ga=m[1]+m[2],m[0]+m[2],m[0]+m[1]
key = nu*((al-be-ga)*(al-be+ga)*(al+be-ga))
print('h8', sp.expand(nu*m[0]*m[1]*m[2] - sp.Rational(-1,8)*key))
# PS_f final
a1,a2,a3=sp.symbols('a1:4'); sg=sp.symbols('sg0:4'); zz=sp.symbols('zz0:4')
u=[sp.symbols('u%d_0:4'%k) for k in range(3)]
S=a1+a2+a3
fv=[a1-S/4,a2-S/4,a3-S/4,-S/4]
lhs = sum(zz[i]*(sg[0]*u[0][i]+sg[1]*u[1][i]+sg[2]*u[2][i]) for i in range(4))
goal = lhs - mj*ip(fv,sg)
q=[sum(zz[i]*u[k][i] for i in range(4)) - [a1,a2,a3][k]*mj for k in range(3)]
comb = sg[0]*q[0]+sg[1]*q[1]+sg[2]*q[2] + (mj*S/4)*tau(sg)
print('PS_f', sp.expand(goal-comb))
