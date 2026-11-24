import sympy as sp, re
u=sp.symbols('u0:4'); p=sp.symbols('p0:4'); q=sp.symbols('q0:4'); r=sp.symbols('r0:4'); v=sp.symbols('v0:4'); a,b,T=sp.symbols('a b T')
tau=lambda x: sum(x)
ip=lambda x,y: sum(x[i]*y[i] for i in range(4))
t3=lambda x,y,z: sum(x[i]*y[i]*z[i] for i in range(4))
def X3c(z1,z2,z3,z4):
    def f(x,y,z): return tau(x)*tau(y)*tau(z)-tau(x)*ip(y,z)-tau(y)*ip(x,z)-tau(z)*ip(x,y)+2*t3(x,y,z)
    return f(z1,z2,z3)+f(z1,z2,z4)+f(z1,z3,z4)+f(z2,z3,z4)
add=lambda x,y:[x[i]+y[i] for i in range(4)]; sm=lambda c,x:[c*xi for xi in x]
l2,l3,l4=a,b,-(a+b)
fp=X3c(u,add(p,sm(l2,v)),add(q,sm(l3,v)),add(r,sm(l4,v)))
fm=X3c(u,add(p,sm(-l2,v)),add(q,sm(-l3,v)),add(r,sm(-l4,v)))
f0=X3c(u,p,q,r)
e2l=l2*l3+l2*l4+l3*l4
F2=2*(e2l*t3(u,v,v)+l2*l3*t3(v,v,r)+l2*l4*t3(v,v,q)+l3*l4*t3(v,v,p))
D=sp.expand(fp+fm-2*f0-2*F2)   # = 2*(f2 - F2)
sub={v[0]:T-v[1]-v[2]-v[3]}
Ds=sp.expand(D.subs(sub))
D0=sp.expand(Ds.subs(T,0))
A=sp.expand(sp.cancel((Ds-D0)/T))
ivv=sp.expand(ip(v,v).subs(sub).subs(T,0))
B,C=sp.div(D0,ivv,*(v[1],v[2],v[3]))
print('remainder', sp.expand(C)==0)
# back-substitute T -> tau v
Ab=sp.expand(A.subs(T,sum(v))); Bb=sp.expand(B)
# Note: B was computed with v0 eliminated; identity D = A*(tau v) + B*ivv must hold with v0 eliminated; verify in full vars
chk=sp.expand(D - Ab*sum(v) - Bb*ip(v,v))
print('full check', chk==0)
import pickle; pickle.dump((Ab,Bb),open('s8c.pkl','wb'))
cs=sp.expand(chk.subs(sub))
print('cs at T=0:', sp.expand(cs.subs(T,0))==0)
A2=sp.expand(sp.cancel(cs/T))
Afin=sp.expand(Ab + A2.subs(T,sum(v)))
chk2=sp.expand(D - Afin*sum(v) - Bb*ip(v,v))
print('full check 2', chk2==0)
pickle.dump((Afin,Bb),open('s8c.pkl','wb'))
print(len(str(Afin)), len(str(Bb)))
