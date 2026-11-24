import sympy as sp, itertools, random
# 1) pc_Qv3 check with v = r*chi
r=sp.Rational(3,2); I=sp.I
v=[r, r*I, -r, -r*I]; kap=sp.expand(r**4)
A=sp.symbols('A0:3'); L=sp.symbols('L0:3'); B=sp.symbols('B0:3')
Qv=lambda a0,a1,a2,a3: [a0+a1*x+a2*x**2+a3*x**3 for x in v]
def pc(z1,z2,z3,z4): return sum(z1[i]*z2[j]*z3[k]*z4[l] for i,j,k,l in itertools.permutations(range(4)))
cols=[[1+e for e in Qv(A[j],L[j],B[j],0)] for j in range(3)]
lhs=sp.expand(pc(cols[0],cols[1],cols[2],[1]*4))
tau=[4*A[j] for j in range(3)]
Ip=lambda i,j: 4*(A[i]*A[j]+kap*B[i]*B[j])
T=4*(A[0]*A[1]*A[2]+kap*(B[0]*B[1]*A[2]+B[0]*A[1]*B[2]+A[0]*B[1]*B[2]+B[0]*L[1]*L[2]+L[0]*B[1]*L[2]+L[0]*L[1]*B[2]))
rhs=24+6*sum(tau)+2*(tau[0]*tau[1]+tau[0]*tau[2]+tau[1]*tau[2])-2*(Ip(0,1)+Ip(0,2)+Ip(1,2))+(tau[0]*tau[1]*tau[2]-tau[0]*Ip(1,2)-tau[1]*Ip(0,2)-tau[2]*Ip(0,1)+2*T)
print('pc_Qv3', sp.expand(lhs-rhs))
# 2) final algebra certificate
p0,p1,l1,m0,m1=sp.symbols('p0 p1 l1 m0 m1')
p=[p0,p1,-p0-p1]; l=[1,l1,-1-l1]; m=[m0,m1,-m0-m1]
Q=lambda x: m[0]*x[1]*x[2]+m[1]*x[0]*x[2]+m[2]*x[0]*x[1]
Bf=lambda x,y: sp.Rational(1,2)*(Q([x[k]+y[k] for k in range(3)])-Q(x)-Q(y))
det=m0*m1-m[2]**2
w=p0*l[1]-p1*l[0]
Rq,rem=sp.div(sp.expand(Q(p)-p0**2*Q(l)),sp.expand(w),p0)
print('rem', sp.simplify(rem))
R=sp.expand(Rq)
c1=det*p0**2*Q(p)+det*p0**2*w*R+Q(p)*R**2
c2=-Bf(p,l)*R**2
print('cert', sp.expand(det*Q(p)**2-c1*Q(l)-c2*Bf(p,l)))
print('R =', sp.factor(R))
print('det =', sp.factor(det), ' vs <m,m>/2 =', sp.factor(sp.expand((m0**2+m1**2+m[2]**2)/2)))
