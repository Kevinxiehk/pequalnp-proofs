import sympy as sp, re
v=list(sp.symbols('v0:4')); w=list(sp.symbols('w0:4')); c2,c3,g=sp.symbols('c2 c3 g')
S2,S3=sp.symbols('S2 S3')
tau=lambda a:sum(a)
ip=lambda a,b:sum(x*y for x,y in zip(a,b))
t3=lambda a,b,c:sum(a[i]*b[i]*c[i] for i in range(4))
def X3c(z1,z2,z3,z4):
    T=tau
    return ((T(z1)*T(z2)*T(z3)-T(z1)*ip(z2,z3)-T(z2)*ip(z1,z3)-T(z3)*ip(z1,z2)+2*t3(z1,z2,z3))
     +(T(z1)*T(z2)*T(z4)-T(z1)*ip(z2,z4)-T(z2)*ip(z1,z4)-T(z4)*ip(z1,z2)+2*t3(z1,z2,z4))
     +(T(z1)*T(z3)*T(z4)-T(z1)*ip(z3,z4)-T(z3)*ip(z1,z4)-T(z4)*ip(z1,z3)+2*t3(z1,z3,z4))
     +(T(z2)*T(z3)*T(z4)-T(z2)*ip(z3,z4)-T(z3)*ip(z2,z4)-T(z4)*ip(z2,z3)+2*t3(z2,z3,z4)))
def L(e):
    s=sp.sstr(sp.expand(e)).replace('**','^')
    s=re.sub(r'\bv(\d)\b',r'v \1',s); s=re.sub(r'\bw(\d)\b',r'w \1',s)
    return s
u=[-(c2*v[k]+c3*w[k])/2 for k in range(4)]
P=sp.expand(X3c(u,u,[c2*x for x in v],[0,0,0,0]))
r0,r1,r2=t3(v,v,v),t3(v,v,w),t3(v,w,w)
Q=sp.expand(P-(c2/2)*(c2**2*r0+2*c2*c3*r1+c3**2*r2))
# Q lies in ideal (tau v, tau w): substitute v3 = S2 - v0-v1-v2, w3 = S3 - ...
sub={v[3]:S2-v[0]-v[1]-v[2], w[3]:S3-w[0]-w[1]-w[2]}
Qs=sp.expand(Q.subs(sub))
assert sp.expand(Qs.subs({S2:0,S3:0}))==0
A=sp.expand(sp.cancel((Qs-Qs.subs(S2,0))/S2)); rest=sp.expand(Qs.subs(S2,0)); B=sp.expand(sp.cancel(rest/S3))
back={S2:sum(v),S3:sum(w)}
A=sp.expand(A.subs(back)); B=sp.expand(B.subs(back))
chk=sp.expand(P-(c2/2)*(c2**2*r0+2*c2*c3*r1+c3**2*r2)-A*tau(v)-B*tau(w))
print('X3c_two check',chk, 'sizes',len(sp.Add.make_args(A)),len(sp.Add.make_args(B)))
open('x3c_two.cert','w').write(f'({L(A)}) * hv + ({L(B)}) * hw + ({L(c2**3/2)}) * r0 + ({L(c2**2*c3)}) * r1 + ({L(c2*c3**2/2)}) * r2')
# e3 certificate: hA_k: v_k w_k - g/4 ; tau w ; goal g*e3(v) = 0
e3=v[0]*v[1]*v[2]+v[0]*v[1]*v[3]+v[0]*v[2]*v[3]+v[1]*v[2]*v[3]
hA=[v[k]*w[k]-g/4 for k in range(4)]
prods=[v[1]*v[2]*v[3],v[0]*v[2]*v[3],v[0]*v[1]*v[3],v[0]*v[1]*v[2]]
P4=v[0]*v[1]*v[2]*v[3]
# sum_k prods_k * hA_k = tau(w)*P4 - g/4 * e3  => g*e3 = 4*(tau(w) P4 - sum prods_k hA_k)
print('e3 check',sp.expand(g*e3-(4*P4*tau(w)-4*sum(prods[k]*hA[k] for k in range(4)))))
# t3 v v v = 3 e3 + tau(v)*(...): p3 = e1^3 - 3 e1 e2 + 3 e3
e1=tau(v); e2=sum(v[i]*v[j] for i in range(4) for j in range(i+1,4))
print('p3 check',sp.expand(r0-(e1**3-3*e1*e2+3*e3)))
