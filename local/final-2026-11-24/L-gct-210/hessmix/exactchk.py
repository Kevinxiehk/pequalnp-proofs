# exact (Fraction) Schwartz-Zippel check of the u-coordinate formulas for P2, P3, P4 on sum-zero t
import sys, random; sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
from fractions import Fraction as F
from level import Pk_exact
random.seed(7)
def Phi(t):
    m=sum(map(sum,t))/F(25)
    al=[sum(t[i])/F(5)-m for i in range(5)]; be=[sum(t[i][j] for i in range(5))/F(5)-m for j in range(5)]
    g=[[t[i][j]-m-al[i]-be[j] for j in range(5)] for i in range(5)]
    return [[g[i][j]-F(3,2)*(al[i]+be[j]) for j in range(5)] for i in range(5)]
def mm(A,B): return [[sum(A[i][k]*B[k][j] for k in range(5)) for j in range(5)] for i in range(5)]
def T(A): return [[A[j][i] for j in range(5)] for i in range(5)]
ok=True
for trial in range(12):
    t=[[F(random.randint(-10**6,10**6)) for j in range(5)] for i in range(5)]
    s=sum(map(sum,t)); t[4][4]-=s   # sum zero
    P=Pk_exact(t); u=Phi(t)
    R=[sum(u[i]) for i in range(5)]; C=[sum(u[i][j] for i in range(5)) for j in range(5)]
    r=[sum(x*x for x in u[i]) for i in range(5)]; c=[sum(u[i][j]**2 for i in range(5)) for j in range(5)]
    p2=sum(x*x for row in u for x in row); p3=sum(x**3 for row in u for x in row); p4=sum(x**4 for row in u for x in row)
    uC=[sum(u[i][j]*C[j] for j in range(5)) for i in range(5)]; uR=[sum(u[i][j]*R[i] for i in range(5)) for j in range(5)]
    M=mm(u,T(u)); tr4=sum(M[i][k]*M[k][i] for i in range(5) for k in range(5))
    S2R=sum(x*x for x in R); S2C=sum(x*x for x in C)
    e2=2*P[2]-(p2-F(5,9)*(S2R+S2C))
    e3=P[3]-F(2,3)*(p3-F(1,9)*(sum(x**3 for x in R)+sum(x**3 for x in C)))
    P4=(F(3,2)*p4-F(3,4)*(sum(x*x for x in r)+sum(x*x for x in c))+p2*p2/8+tr4/4
        -F(7,108)*(sum(x**4 for x in R)+sum(x**4 for x in C))+F(7,216)*(S2R**2+S2C**2)+F(1,36)*S2R*S2C-F(1,12)*p2*(S2R+S2C)
        +F(1,2)*(sum(R[i]**2*r[i] for i in range(5))+sum(C[j]**2*c[j] for j in range(5)))
        -F(2,3)*sum((R[i]+C[j])*u[i][j]**3 for i in range(5) for j in range(5))
        +F(2,9)*sum(R[i]*u[i][j]**2*C[j] for i in range(5) for j in range(5))
        -F(1,9)*(sum(R[i]**2*uC[i] for i in range(5))+sum(C[j]**2*uR[j] for j in range(5)))
        -F(1,6)*(sum(x*x for x in uR)+sum(x*x for x in uC))
        +F(1,3)*(sum(uC[i]*r[i] for i in range(5))+sum(uR[j]*c[j] for j in range(5))))
    e4=P[4]-P4
    if e2!=0 or e3!=0 or e4!=0: ok=False; print('FAIL',trial,e2,e3,e4)
print('exact identities P2,P3,P4 at 12 random integer sum-zero points:', 'ALL EXACT' if ok else 'FAILED')
