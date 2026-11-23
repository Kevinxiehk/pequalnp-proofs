import random
def rnd(): return complex(random.uniform(-1,1), random.uniform(-1,1))
kap,be0,be1,be2,pu,ru,pi3,rho3=[rnd() for _ in range(8)]
def br(P,R):
    P1,P2,P3,P4=P; R1,R2,R3,R4=R
    return (-24*kap*(P1*P2*P3*P4)-24*kap**3*(R1*R2*R3*R4)
      +8*kap**2*(P1*P2*R3*R4+P1*P3*R2*R4+P1*P4*R2*R3+P2*P3*R1*R4+P2*P4*R1*R3+P3*P4*R1*R2))
def G(t,x0,x2,pi3):
    P=[t*(be0+pu)/2+x0, t*(be1+pu)/2-x0-x2, t*(be2+pu)/2+x2, t*(pi3+pu)/2]
    R=[t*ru/2]*3+[t*(rho3+ru)/2]
    return br(P,R)
g=lambda t: G(t,1,-2,pi3)
print(abs(8*(g(1)-g(-1))-(g(2)-g(-2)) - 288*kap*(pi3+pu)))
g=lambda t: G(t,1,-2,-pu)
print(abs(16*(g(1)+g(-1))-(g(2)+g(-2)) + 144*kap**2*ru*(rho3+ru)))
