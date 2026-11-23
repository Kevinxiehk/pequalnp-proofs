import random
def rnd(): return complex(random.uniform(-1,1), random.uniform(-1,1))
c=[rnd() for _ in range(5)]; m=[rnd() for _ in range(5)]; D=[rnd() for _ in range(5)]
def f(b):
    return 2*sum(c[j]*sum(m[l] for l in range(5) if l!=b and l!=j) for j in range(5) if j!=b)
M=sum(m); S=sum(c); cm=sum(c[j]*m[j] for j in range(5))
A = m[0]*cm - ((m[0]*S - D[0]/6)*M + (m[0]/6)*sum(D[b]-f(b) for b in range(5)) - (1/6)*sum(m[0]*D[b]-m[b]*D[0] for b in range(1,5)))
print(abs(A))
for b in range(1,5):
    B = 4*m[0]*m[b]*(c[b]-c[0]) - ((m[0]*D[b]-m[b]*D[0]) - m[0]*(D[b]-f(b)) + m[b]*(D[0]-f(0)) - 2*(m[0]*(S-c[b]) - m[b]*(S-c[0]))*M - 2*(m[b]-m[0])*cm)
    print(abs(B))
