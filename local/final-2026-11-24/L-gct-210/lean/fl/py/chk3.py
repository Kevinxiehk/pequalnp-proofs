import random, itertools
def rnd(): return complex(random.uniform(-1,1), random.uniform(-1,1))
x=[rnd() for _ in range(5)]
def E(m):
    o=[j for j in range(5) if j!=m]
    return sum(x[a]*x[b]*x[c] for a,b,c in itertools.combinations(o,3))
p1=sum(x); s=sum(t*t for t in x)/2
for j in range(5):
    lhs=x[j]**3-s*x[j]
    rhs=0.5*sum(E(m) for m in range(5))-E(j)+(x[j]**2-x[j]*p1/2)*p1
    print(abs(lhs-rhs))
