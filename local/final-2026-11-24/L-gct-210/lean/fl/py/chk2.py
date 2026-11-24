import random
def rnd(): return complex(random.uniform(-1,1), random.uniform(-1,1))
a,b,c,d=[rnd() for _ in range(4)]
p1=a+b+c+d; p2=a*a+b*b+c*c+d*d; p3=a**3+b**3+c**3+d**3; p4=a**4+b**4+c**4+d**4
rhs=(a**3-p1/2*a**2+p1**2/6*a-p1**3/24)*p1+(a**2/2-p1/2*a+p1**2/4-p2/8)*p2+(a/3-p1/3)*p3+p4/4
print(abs(a**4-rhs))
