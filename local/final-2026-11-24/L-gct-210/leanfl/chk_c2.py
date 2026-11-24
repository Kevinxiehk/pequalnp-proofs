import sympy as sp, itertools
v=list(sp.symbols('v0:4')); w=list(sp.symbols('w0:4')); l3,l4,b=sp.symbols('l3 l4 b')
# impose tau=0 by substitution, isotropy kept symbolic via reduction
sub={v[3]:-v[0]-v[1]-v[2], w[3]:-w[0]-w[1]-w[2]}
V=[x.subs(sub) for x in v]; W=[x.subs(sub) for x in w]
tau=lambda a:sum(a); ip=lambda a,c:sum(p*q for p,q in zip(a,c)); t3=lambda a,c,d:sum(a[i]*c[i]*d[i] for i in range(4))
t4=lambda a,c,d,e:sum(a[i]*c[i]*d[i]*e[i] for i in range(4))
def X3c(z1,z2,z3,z4):
    T=tau
    return ((T(z1)*T(z2)*T(z3)-T(z1)*ip(z2,z3)-T(z2)*ip(z1,z3)-T(z3)*ip(z1,z2)+2*t3(z1,z2,z3))
     +(T(z1)*T(z2)*T(z4)-T(z1)*ip(z2,z4)-T(z2)*ip(z1,z4)-T(z4)*ip(z1,z2)+2*t3(z1,z2,z4))
     +(T(z1)*T(z3)*T(z4)-T(z1)*ip(z3,z4)-T(z3)*ip(z1,z4)-T(z4)*ip(z1,z3)+2*t3(z1,z3,z4))
     +(T(z2)*T(z3)*T(z4)-T(z2)*ip(z3,z4)-T(z3)*ip(z2,z4)-T(z4)*ip(z2,z3)+2*t3(z2,z3,z4)))
def pc(a,c,d,e): return sum(a[i]*c[j]*d[k]*e[l] for i,j,k,l in itertools.permutations(range(4)))
a=l3+l4
u=[-(a*V[k]+b*W[k])/2 for k in range(4)]
T3_,T21,T12,T03=t3(V,V,V),t3(V,V,W),t3(V,W,W),t3(W,W,W); g=ip(V,W)
y2=[l3*x for x in V]; y3=[l4*x for x in V]; y4=[b*x for x in W]
tu2v=t3(u,u,V); tu2w=t3(u,u,W); tuv2=t3(u,V,V); tuvw=t3(u,V,W)
chk=lambda name,e: print(name, sp.expand(e)==0)
chk('tau(u^2v)', tu2v-(a**2*T3_+2*a*b*T21+b**2*T12)/4)
chk('tau(u^2w)', tu2w-(a**2*T21+2*a*b*T12+b**2*T03)/4)
chk('tau(uv^2)', tuv2+(a*T3_+b*T21)/2)
chk('tau(uvw)', tuvw+(a*T21+b*T12)/2)
chk('Tbar1', X3c(u,y2,y3,y4)/2 + (l3*l4*(a*T3_-b*T21)+a*b*(a*T21+b*T12))/2)
chk('Tbar5', X3c(u,u,y2,y3)/2-(a*tu2v+2*l3*l4*tuv2))
chk('Tbar3', X3c(u,u,y3,y4)/2-(l4*tu2v+b*tu2w+2*l4*b*tuvw))
chk('Tbar4', X3c(u,u,y2,y4)/2-(l3*tu2v+b*tu2w+2*l3*b*tuvw))
# quartic: with isotropy ip(V,V)=ip(W,W)=0 -> reduce modulo these
Q=sp.expand(pc(u,y2,y3,y4)-l3*l4*b*(3*t4(V,V,V,W)*a+(3*t4(V,V,W,W)-g**2)*b))
G=sp.groebner([sp.expand(ip(V,V)),sp.expand(ip(W,W))],*V[:3],*W[:3],l3,l4,b,order='grevlex')
print('quartic mod isotropy', G.reduce(Q)[1]==0)
