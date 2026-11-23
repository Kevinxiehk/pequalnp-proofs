import itertools, random
def rnd(): return complex(random.uniform(-1,1), random.uniform(-1,1))
def tau(z): return sum(z)
def ip(x,y): return sum(a*b for a,b in zip(x,y))
def t3(x,y,z): return sum(a*b*c for a,b,c in zip(x,y,z))
def t4(x,y,z,w): return sum(a*b*c*d for a,b,c,d in zip(x,y,z,w))
def pc(z1,z2,z3,z4):
    return sum(z1[p[0]]*z2[p[1]]*z3[p[2]]*z4[p[3]] for p in itertools.permutations(range(4)))
def br(x,y,z,w): return -6*t4(x,y,z,w)+ip(x,y)*ip(z,w)+ip(x,z)*ip(y,w)+ip(x,w)*ip(y,z)
z=[[rnd() for _ in range(4)] for _ in range(4)]
c=rnd()
z1,z2,z3,z4=z
T=[tau(v) for v in z]
lhs=pc(*[[1+c*x for x in v] for v in z])
X1=6*sum(T)
X2=2*(T[0]*T[1]+T[0]*T[2]+T[0]*T[3]+T[1]*T[2]+T[1]*T[3]+T[2]*T[3])-2*(ip(z1,z2)+ip(z1,z3)+ip(z1,z4)+ip(z2,z3)+ip(z2,z4)+ip(z3,z4))
def e3(a,b,c_):
    return tau(a)*tau(b)*tau(c_)-tau(a)*ip(b,c_)-tau(b)*ip(a,c_)-tau(c_)*ip(a,b)+2*t3(a,b,c_)
X3=e3(z1,z2,z3)+e3(z1,z2,z4)+e3(z1,z3,z4)+e3(z2,z3,z4)
X4=pc(*z)
print(abs(lhs-(24+c*X1+c**2*X2+c**3*X3+c**4*X4)))
g=(T[0]*T[1]*T[2]*T[3]
 -(ip(z1,z2)*T[2]*T[3]+ip(z1,z3)*T[1]*T[3]+ip(z1,z4)*T[1]*T[2]+ip(z2,z3)*T[0]*T[3]+ip(z2,z4)*T[0]*T[2]+ip(z3,z4)*T[0]*T[1])
 +2*(T[0]*t3(z2,z3,z4)+T[1]*t3(z1,z3,z4)+T[2]*t3(z1,z2,z4)+T[3]*t3(z1,z2,z3))
 +br(*z))
print(abs(X4-g))
