import sympy as sp
v=sp.symbols('v0:4'); w=sp.symbols('w0:4'); s=sp.Symbol('s')
h=sp.symbols('h1:7')
g=sum(a*b for a,b in zip(v,w)); A=sum(a**3 for a in v); B=sum(b**3 for b in w)
p1=h[0]+s*h[1]; p2=h[2]+2*s*g+s**2*h[3]; p3=A+3*s*h[4]+3*s**2*h[5]+s**3*B
def H(k):
    u=v[k]+s*w[k]
    return u**4-p1*u**3+(p1**2-p2)/2*u**2-(p1**3-3*p1*p2+2*p3)/6*u
y=[v[k]*w[k] for k in range(4)]
actual={h[0]:sum(v),h[1]:sum(w),h[2]:sum(a*a for a in v),h[3]:sum(b*b for b in w),
        h[4]:sum(v[k]**2*w[k] for k in range(4)),h[5]:sum(v[k]*w[k]**2 for k in range(4))}
out={}
for k in (1,2,3):
    D=sp.expand(H(k)-H(0)).coeff(s,2)
    E2=sp.expand(6*y[k]**2-2*g*y[k]-6*y[0]**2+2*g*y[0])
    R=sp.expand(D-E2)   # h-terms
    # split R into sum c_i h_i : take derivative-free decomposition by assigning each monomial to first h present
    P=sp.Poly(R,*h)
    cs=[0]*6
    for mon,coef in P.terms():
        i=next(j for j in range(6) if mon[j]>0)
        m=list(mon); m[i]-=1
        cs[i]+=coef*sp.prod([h[j]**m[j] for j in range(6)])
    cs=[sp.expand(c.subs(actual)) for c in cs]
    # check: E2 + sum c_i * actual_i == D|actual == 0 ?
    chk=sp.expand(E2+sum(cs[i]*actual[h[i]] for i in range(6)))
    print(k,'check',chk,'sizes',[len(sp.Add.make_args(c)) for c in cs])
    out[k]=cs
import pickle; pickle.dump(out,open('e2cert.pkl','wb'))
