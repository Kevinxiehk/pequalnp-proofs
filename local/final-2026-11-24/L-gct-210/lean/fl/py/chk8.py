import random
def rnd(): return complex(random.uniform(-1,1), random.uniform(-1,1))
c=[rnd() for _ in range(5)]; m=[rnd() for _ in range(5)]; D=[rnd() for _ in range(5)]
M=sum(m); S=sum(c); cm=sum(c[j]*m[j] for j in range(5))
def f(b):
    return 2*sum(c[j]*sum(m[l] for l in range(5) if l!=b and l!=j) for j in range(5) if j!=b)
def closed(b): return -2*S*m[b]+4*c[b]*m[b]-2*cm
for b in range(5):
    print(abs((D[b]-closed(b)) - ((D[b]-f(b)) + 2*(S-c[b])*M)))
b0=2
L=[m[b0]*D[b]-m[b]*D[b0] for b in range(5)]
G=[D[b]-closed(b) for b in range(5)]
print(abs(m[b0]*cm - (-(1/6)*sum(L) - (1/6)*D[b0]*M + (m[b0]/6)*sum(G) - (1/3)*m[b0]*S*M)))
b=4
print(abs(4*m[b]*m[b0]*(c[b]-c[b0]) - (L[b] - m[b0]*G[b] + m[b]*G[b0] + 2*(m[b0]-m[b])*cm)))
