import random
def rnd(): return complex(random.uniform(-1,1), random.uniform(-1,1))
u=[rnd() for _ in range(5)]; v=[rnd() for _ in range(5)]; w=[rnd() for _ in range(5)]
U=sum(u); V=sum(v); Wt=sum(w); P=sum(u[j]*v[j] for j in range(5))
uw=sum(u[j]*w[j] for j in range(5)); vw=sum(v[j]*w[j] for j in range(5)); t3=sum(u[j]*v[j]*w[j] for j in range(5))
def f(b):
    idx=[j for j in range(5) if j!=b]
    return 2*sum((1+u[j])*sum(1+v[l] for l in idx if l!=j) for j in idx)
h=sum(w[b]*f(b) for b in range(5))
cert=(1/4)*h-(1/2)*(12+3*U+3*V+U*V-P)*Wt+(3/2)*uw+(3/2)*vw+(1/2)*U*vw+(1/2)*V*uw
print(abs(t3-cert))
