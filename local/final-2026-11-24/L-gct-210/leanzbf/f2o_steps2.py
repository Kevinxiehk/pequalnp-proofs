import sympy as sp
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/lcfind.py').read())
j, c, cp, A1, A2, A3 = sp.symbols('j c cp A1 A2 A3')
V = [j, c, cp, A1, A2, A3]
H = {'hj': j*j + 1,
     'E1': A1 + A2 + A3 - 1, 'E2': c*(j*A1 + A2 - A3) - 1, 'E3': cp*(-A1 + A2 + j*A3) - 1,
     'E4': (A3 + c*A2)*(1 + j) - 1, 'E5': (A1 + cp*A2)*(1 + j) - 1, 'E6': j*(c*A1 + cp*A3)*(1 + j) - 1}
F2 = (c - cp)*(j + A2*(1 + c + cp))
r = find_lc(F2, {k: H[k] for k in ('hj', 'E1', 'E2', 'E3', 'E4', 'E5')}, V, 2); print('F2', r)
