import random, itertools
def perm3(M):
    s=0
    for p in itertools.permutations(range(3)):
        s+=M[0][p[0]]*M[1][p[1]]*M[2][p[2]]
    return s
random.seed(1)
for trial in range(5):
    r=lambda: complex(random.randint(-9,9),random.randint(-9,9)) or 1
    k0=[r(),r(),r()]; d2=r(); c=r(); j=1j*random.choice([1,-1])
    T,A1,A2,A3=r(),r(),r(),r()
    K=[k0,[d2*k0[0],-d2*k0[1],-d2*k0[2]],[-c*k0[0],c*j*k0[1],c*k0[2]]]
    tau=[[T,A1,-T-A1],[T,A2,-T-A2],[A3,T-A3,-T]]
    x=[[tau[i][jj]/K[i][jj] for jj in range(3)] for i in range(3)]
    lhs=d2*c*k0[0]*k0[1]*k0[2]*perm3(x)
    rhs=(A2-A1)*T*(T-j*(T-A3))-A3*(T*(A1+A2)+2*A1*A2)
    print(abs(lhs-rhs), abs(lhs+rhs))
