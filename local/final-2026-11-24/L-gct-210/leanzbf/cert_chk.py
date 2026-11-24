import sympy as sp
c, cp, cpp, cJ, j, w, w2, k, A1, A2, A3, k2, k3 = sp.symbols('c cp cpp cJ j w w2 k A1 A2 A3 k2 k3')
hj = j*j + 1; hcJ = cJ - j*c
def chk(name, goal, comb):
    r = sp.expand(goal - comb); print(name, 'OK' if r == 0 else r)
# orientation 1
R1 = cp - cpp*cJ; R2 = w + cpp*c; R3 = -cp + w2*c
chk('o1 hw', w - j*cp, R2 - j*R1 - cpp*j*hcJ - cpp*c*hj)
chk('o1 hw2', (w2 - j*cpp)*c, R3 + R1 + cpp*hcJ)
# witness R's (k = kappa at point, k2 = kappa2, k3 = kappa3)
chk('o1 R1', cp*k - cpp*cJ*k, -(k3 - cp*k) + (k3 - cpp*k2) + cpp*(k2 - cJ*k))
chk('o1 R2', w*k - (-cpp*c)*k, -(k3 - w*k) + (k3 - (-cpp)*k2) + (-cpp)*(k2 - c*k))
chk('o1 R3', -cp*k - w2*(-c)*k, -(k3 - (-cp)*k) + (k3 - w2*k2) + w2*(k2 - (-c)*k))
S2 = cJ*A1 + c*A2 + (-c)*A3 - 1
chk('o1 E2', c*(j*A1 + A2 - A3) - 1, S2 - A1*hcJ)
S3 = cp*A1 + w*A2 + (-cp)*A3 - 1
chk('o1 E3', cp*(A1 + j*A2 - A3) - 1, S3 - A2*(w - j*cp))
J12 = (A3 + c*A2)*(cJ + c) - c
chk('o1 E4', c*((A3 + c*A2)*(1 + j) - 1), J12 - (A3 + c*A2)*hcJ)
J13 = (A3 + cp*A1)*(w + cp) - cp
chk('o1 E5', cp*((A3 + cp*A1)*(1 + j) - 1), J13 - (A3 + cp*A1)*(w - j*cp))
J23 = (c*A2 + cp*A1)*(w2 + cpp) - cpp
chk('o1 E6', cpp*((c*A2 + cp*A1)*(1 + j) - 1), J23 - (c*A2 + cp*A1)*(w2 - j*cpp))
e2 = (j*j + 1)*c**2
chk('hj', e2, (cJ**2 + c**2) - (cJ + j*c)*hcJ)
# orientation 2
R1 = -cp + cpp*cJ; R2 = cp - w2*c; R3 = w + cpp*c
chk('o2 R1', -cp*k - (-cpp*cJ)*k, -(k3 - (-cp)*k) + (k3 - (-cpp)*k2) + (-cpp)*(k2 - cJ*k))
chk('o2 R2', cp*k - w2*c*k, -(k3 - cp*k) + (k3 - w2*k2) + w2*(k2 - c*k))
chk('o2 R3', w*k - cpp*(-c)*k, -(k3 - w*k) + (k3 - cpp*k2) + cpp*(k2 - (-c)*k))
chk('o2 hw', w - j*cp, R3 + j*R1 - cpp*j*hcJ - cpp*c*hj)
chk('o2 hw2', (w2 - j*cpp)*c, -R2 - R1 + cpp*hcJ)
S3 = (-cp)*A1 + cp*A2 + w*A3 - 1
chk('o2 E3', cp*(-A1 + A2 + j*A3) - 1, S3 - A3*(w - j*cp))
J13 = (A1 + cp*A2)*(w + cp) - cp
chk('o2 E5', cp*((A1 + cp*A2)*(1 + j) - 1), J13 - (A1 + cp*A2)*(w - j*cp))
J23 = (cJ*A1 + w*A3)*(w2 + cpp) - cpp
chk('o2 E6', cpp*(j*(c*A1 + cp*A3)*(1 + j) - 1), J23 - (w2 + cpp)*A1*hcJ - (w2 + cpp)*A3*(w - j*cp) - (j*c*A1 + j*cp*A3)*(w2 - j*cpp))
