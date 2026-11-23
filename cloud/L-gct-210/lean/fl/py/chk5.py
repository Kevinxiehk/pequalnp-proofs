import random, itertools
def rnd(): return complex(random.uniform(-1,1), random.uniform(-1,1))
l=[rnd() for _ in range(5)]; t=[rnd() for _ in range(5)]
def tau3(a,b,c): return 4*(a+b+c)+a*b*c*(a*b+b*c+c*a)
def kk(x,y): return 2*x+4*y+x**2*y**3+x*y**4/2
def T(m):
    o=[k for k in range(5) if k!=m]
    return sum(l[a]*l[b]*l[c]*tau3(t[a],t[b],t[c]) for a,b,c in itertools.combinations(o,3))
H0=sum(l); H1=sum(l[k]*t[k] for k in range(5)); H2=sum(l[k]*t[k]**2 for k in range(5))
for m in range(5):
    FF=(12*t[m]+3*t[m]**5)*l[m]**2-sum(l[a]**2*kk(t[m],t[a]) for a in range(5))
    th=t[m]; lm=l[m]
    R=H0*(2*th*H0+4*H1-8*lm*th)+H1*(th**2*H2-lm*th**4-4*lm)+H2*(th*H2/2-2*lm*th**3)
    rhs=0.5*sum(T(n) for n in range(5))-T(m)-lm*R
    print(abs(lm*FF-rhs))
# check kk = tau3(x,y,y)/2 and c = tau3(x,x,x)
x,y=rnd(),rnd(); print(abs(kk(x,y)-tau3(x,y,y)/2), abs(tau3(x,x,x)-(12*x+3*x**5)))
