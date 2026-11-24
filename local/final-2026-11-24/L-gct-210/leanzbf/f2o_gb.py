import sympy as sp
j, c, cp, A1, A2, A3, z, w = sp.symbols('j c cp A1 A2 A3 z w')
hj = j**2 + 1
def run(name, eqs):
    G = sp.groebner(eqs + [hj, c*z - 1, cp*w - 1], z, w, A1, A2, A3, c, cp, j, order='lex')
    print(name, 'GB:', list(G)[:6], '...' if len(G) > 6 else '')
o1 = [A1 + A2 + A3 - 1, c*(j*A1 + A2 - A3) - 1, cp*(A1 + j*A2 - A3) - 1,
      (A3 + c*A2)*(1 + j) - 1, (A3 + cp*A1)*(1 + j) - 1, (c*A2 + cp*A1)*(1 + j) - 1]
o2 = [A1 + A2 + A3 - 1, c*(j*A1 + A2 - A3) - 1, cp*(-A1 + A2 + j*A3) - 1,
      (A3 + c*A2)*(1 + j) - 1, (A1 + cp*A2)*(1 + j) - 1, j*(c*A1 + cp*A3)*(1 + j) - 1]
run('orient1', o1)
run('orient2', o2)
