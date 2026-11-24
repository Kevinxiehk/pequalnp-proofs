import random, itertools
def perm3(M):
    return sum(M[0][p[0]]*M[1][p[1]]*M[2][p[2]] for p in itertools.permutations(range(3)))
random.seed(2)
for trial in range(5):
    r=lambda: complex(random.randint(-9,9),random.randint(-9,9)) or 1
    k0=[r(),r(),r()]; d2=r(); c=r(); j=r()
    T,A1,A2,A3=r(),r(),r(),r()
    x=[[T/k0[0],A1/k0[1],(-T-A1)/k0[2]],
       [T/(d2*k0[0]),A2/(-d2*k0[1]),(-T-A2)/(-d2*k0[2])],
       [A3/(-c*k0[0]),-j*(T-A3)/(c*k0[1]),-T/(c*k0[2])]]
    lhs=d2*c*k0[0]*k0[1]*k0[2]*perm3(x)
    rhs=(A2-A1)*T*(T-j*(T-A3))-A3*(T*(A1+A2)+2*A1*A2)
    print(abs(lhs-rhs))
