import sympy as sp
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/lcfind.py').read())
j, c, cp, A1, A2, A3 = sp.symbols('j c cp A1 A2 A3')
# verify H6 hand certificate
E6 = j*(c*A1 + cp*A3)*(1 + j) - 1
G4 = 2*A3 - (1 - j - 2*c*A2); G5 = 2*A1 - (1 - j - 2*cp*A2); hj = j*j + 1
H6 = j*(c + cp) - 2*j*(1 + j)*c*cp*A2 - 1
print('H6 check', sp.expand(H6 - (E6 - j*(1 + j)*c/2*G5 - j*(1 + j)*cp/2*G4 + j*(c + cp)/2*hj)))
W = [j, c, A2]
G1c = A2*(1 - 2*c) - j
H2c = c*(j + A2*(1 + c - j*c)) - 1
H6c = 2*j*c - 2*j*(1 + j)*c**2*A2 - 1
r = find_lc(sp.Integer(1), {'G1c': G1c, 'H2c': H2c, 'H6c': H6c, 'hj': hj}, W, 3)
def lean(e):
    s = sp.sstr(sp.expand(e)).replace('**', ' ^ ')
    return s
parts = [f'({lean(v)}) * {k}' for k, v in r.items()]
print('FINAL', ' + '.join(parts))
