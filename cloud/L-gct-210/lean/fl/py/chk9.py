import random, itertools
def rnd(): return complex(random.uniform(-1,1), random.uniform(-1,1))
def pc(z1,z2,z3,z4):
    return sum(z1[p[0]]*z2[p[1]]*z3[p[2]]*z4[p[3]] for p in itertools.permutations(range(4)))
d=[rnd() for _ in range(4)]
a=[rnd() for _ in range(3)]; a.append(-sum(a))
b=[rnd() for _ in range(3)]; b.append(-sum(b))
tau=lambda x: sum(x)
ip=lambda x,y: sum(x[i]*y[i] for i in range(4))
e2=(tau(d)**2-ip(d,d))/2
E=[e2-tau(d)*d[k]+d[k]**2 for k in range(4)]
lhs=pc(d,d,[1+x for x in a],[1+x for x in b])
rhs=4*e2+2*ip([a[k]+b[k] for k in range(4)],E)+pc(d,d,a,b)
print(abs(lhs-rhs))
