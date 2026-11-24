from fractions import Fraction as F
import random
random.seed(7)
def rnd(): return F(random.randint(-9,9), random.randint(1,5))
def run():
    i,y,a,b,c,c2,c3 = [rnd() for _ in range(7)]
    # hypotheses as (L - R)
    hi = i*i + 1
    hy = 2*y - (-1 + i)
    h1 = a + b + c - 1
    h2 = c2*(i*a + b - c) - 1
    h3 = c3*(-a + b + i*c) - 1
    h4 = c + c2*b + y
    h5 = a + c3*b + y
    h6 = i*(c2*a + c3*c) + y
    hA = b*(1 - c2 - c3) - i
    assert hA == h1 - h4 - h5 + hy
    hB = c2*(i + b*(1 + c2 - i*c3)) - 1
    assert hB == h2 - c2*i*h5 + c2*h4 + c2*(i-1)/2*hy + c2/2*hi, 'hB'
    hC = c3*(i + b*(1 + c3 - i*c2)) - 1
    assert hC == h3 + c3*h5 - c3*i*h4 + c3*(i-1)/2*hy + c3/2*hi, 'hC'
    hD = -y*(c2 + c3) - 2*c2*c3*b - i*y
    assert hD == -i*h6 + (c2*a + c3*c)*hi - c2*h5 - c3*h4, 'hD'
    hE = (c2 - c3)*(i + b*(1 + c2 + c3))
    assert hE == hB - hC, 'hE'
    # case A
    hF = i + b*(1 + c2 + c3)
    assert (b - 0) == (hF + hA)/2 - 0 or True
    assert b == (hF + hA)/2, 'caseA b'
    assert i == -hA + (1 - c2 - c3)*b, 'caseA i'
    # case B: c3 = c2
    c3 = c2
    hA = b*(1 - c2 - c2) - i
    hB = c2*(i + b*(1 + c2 - i*c2)) - 1
    hD = -y*(c2 + c2) - 2*c2*c2*b - i*y
    hR1 = (1 - i)*c2**2 + (2 + 2*i)*c2 - 1
    assert hR1 == (1 - 2*c2)*hB - c2*(1 + c2 - i*c2)*hA + c2**2*hi, 'R1'
    hQ2 = c2**2 + i*c2 - (1 + i)/4
    assert hQ2 == F(-1,2)*((1 - 2*c2)*hD + 2*c2**2*hA + (c2*(1 - 2*c2) + i*(1 - 2*c2)/2)*hy + (1 - 2*c2)/2*hi), 'Q2'
    hEE = (1 + i)*c2 - F(1,2)
    assert hEE == hR1 - (1 - i)*hQ2 - (c2 - F(1,4))*hi, 'E'
    fin = F(1,4)
    assert fin == (1 + i)**2*hQ2 - ((1 + i)*c2 + F(1,2) + i*(1 + i))*hEE + (1 + i)/4*hi, 'final'
for _ in range(20): run()
print('all certificates ok')
