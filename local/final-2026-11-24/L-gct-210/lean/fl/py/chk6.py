import random
def rnd(): return complex(random.uniform(-1,1), random.uniform(-1,1))
T=[rnd() for _ in range(5)]; W=[rnd() for _ in range(5)]
def kk(x,y): return 2*x+4*y+x**2*y**3+x*y**4/2
def cc(x): return 12*x+3*x**5
def Fq(m,lam): return cc(T[m])*lam[m]**2-sum(lam[n]**2*kk(T[m],T[n]) for n in range(5))
def pw(j): return sum(W[n]**2*T[n]**j for n in range(5))
X=[T[n]*W[n] for n in range(5)]; WX=[W[n]+X[n] for n in range(5)]
for m in range(5):
    e1=Fq(m,W); e3=Fq(m,X); e12=Fq(m,WX)
    D=4*pw(2)+(pw(5)/2-2*pw(1))*T[m]+(pw(4)/2-2*pw(0))*T[m]**2+(-pw(3))*T[m]**3
    E=4*pw(3)+(2*pw(2)+pw(6)/2)*T[m]+(pw(5)-4*pw(1))*T[m]**2+(-2*pw(0)-pw(4)/2)*T[m]**3+(-pw(3))*T[m]**4
    print(abs(D-(T[m]*e1-0.5*(e12-e1-e3))), abs(E-(T[m]**2*e1-e3)))
s=sum(Fq(m,W) for m in range(5))
d1=pw(5)/2-2*pw(1)
ST=sum(T); ST2=sum(t**2 for t in T)
print(abs(pw(1)-(0.25*s-1.5*d1+ST/2*pw(0)+ST2/4*pw(3)+ST/8*pw(4))))
