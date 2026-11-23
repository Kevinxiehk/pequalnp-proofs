import random
def rnd(): return complex(random.uniform(-1,1), random.uniform(-1,1))
u=[rnd() for _ in range(5)]; v=[rnd() for _ in range(5)]
U=sum(u); V=sum(v); uv=sum(u[j]*v[j] for j in range(5))
def f(b):
    idx=[j for j in range(5) if j!=b]
    return 2*sum((1+u[j])*sum(1+v[l] for l in idx if l!=j) for j in idx)
h=sum(f(b) for b in range(5))-120
print(abs(uv-(-(1/6)*h+4*U+4*V+U*V)))
g=sum(6*sum(1+u[j] for j in range(5) if j!=b) for b in range(5))-120
print(abs(U-g/24))
