import sympy as sp, re
v=list(sp.symbols('v0:4')); w=list(sp.symbols('w0:4')); l3,l4,b=sp.symbols('l3 l4 b')
S2,S3=sp.symbols('S2 S3')
tau=lambda a:sum(a); ip=lambda a,c:sum(p*q for p,q in zip(a,c)); t3=lambda a,c,d:sum(a[i]*c[i]*d[i] for i in range(4))
def X3c(z1,z2,z3,z4):
    T=tau
    return ((T(z1)*T(z2)*T(z3)-T(z1)*ip(z2,z3)-T(z2)*ip(z1,z3)-T(z3)*ip(z1,z2)+2*t3(z1,z2,z3))
     +(T(z1)*T(z2)*T(z4)-T(z1)*ip(z2,z4)-T(z2)*ip(z1,z4)-T(z4)*ip(z1,z2)+2*t3(z1,z2,z4))
     +(T(z1)*T(z3)*T(z4)-T(z1)*ip(z3,z4)-T(z3)*ip(z1,z4)-T(z4)*ip(z1,z3)+2*t3(z1,z3,z4))
     +(T(z2)*T(z3)*T(z4)-T(z2)*ip(z3,z4)-T(z3)*ip(z2,z4)-T(z4)*ip(z2,z3)+2*t3(z2,z3,z4)))
def L(e):
    s=sp.sstr(sp.expand(e)).replace('**','^')
    s=re.sub(r'\bv(\d)\b',r'v \1',s); s=re.sub(r'\bw(\d)\b',r'w \1',s); return s
def cert(P,main):
    Q=sp.expand(P-main)
    sub={v[3]:S2-v[0]-v[1]-v[2], w[3]:S3-w[0]-w[1]-w[2]}
    Qs=sp.expand(Q.subs(sub)); assert sp.expand(Qs.subs({S2:0,S3:0}))==0
    A=sp.expand(sp.cancel((Qs-Qs.subs(S2,0))/S2)); B=sp.expand(sp.cancel(Qs.subs(S2,0)/S3))
    back={S2:sum(v),S3:sum(w)}; A=sp.expand(A.subs(back)); B=sp.expand(B.subs(back))
    assert sp.expand(P-main-A*tau(v)-B*tau(w))==0
    return f'({L(A)}) * hv + ({L(B)}) * hw'
a=l3+l4
u=[-(l3*v[k]+l4*v[k]+b*w[k])/2 for k in range(4)]
T3,T21,T12,T03=t3(v,v,v),t3(v,v,w),t3(v,w,w),t3(w,w,w)
tu2v=(a**2*T3+2*a*b*T21+b**2*T12)/4; tu2w=(a**2*T21+2*a*b*T12+b**2*T03)/4
tuv2=-(a*T3+b*T21)/2; tuvw=-(a*T21+b*T12)/2
y2=[l3*x for x in v]; y3=[l4*x for x in v]; y4=[b*x for x in w]
out={}
out['T5']=cert(sp.expand(X3c(u,u,y2,y3)), 2*(a*tu2v+2*l3*l4*tuv2))
out['T3']=cert(sp.expand(X3c(u,u,y3,y4)), 2*(l4*tu2v+b*tu2w+2*l4*b*tuvw))
out['T4']=cert(sp.expand(X3c(u,u,y2,y4)), 2*(l3*tu2v+b*tu2w+2*l3*b*tuvw))
import json; json.dump(out,open('c2.cert','w'))
# cubN identity exact check
cub=t3(y2,y2,y3)+t3(y2,y2,y4)+t3(y3,y3,y2)+t3(y3,y3,y4)+t3(y4,y4,y2)+t3(y4,y4,y3)+t3(y2,y3,y4)
print('cubN', sp.expand(cub-(l3*l4*(a*T3-b*T21)+a*b*(a*T21+b*T12)))==0)
print({k:len(vv) for k,vv in out.items()})
