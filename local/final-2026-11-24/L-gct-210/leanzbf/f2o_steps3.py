import sympy as sp
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/lcfind.py').read())
j, c, cp, A1, A2, A3 = sp.symbols('j c cp A1 A2 A3')
V = [j, c, cp, A1, A2, A3]
H = {'hj': j*j + 1,
     'E1': A1 + A2 + A3 - 1, 'E2': c*(j*A1 + A2 - A3) - 1, 'E3': cp*(-A1 + A2 + j*A3) - 1,
     'E4': (A3 + c*A2)*(1 + j) - 1, 'E5': (A1 + cp*A2)*(1 + j) - 1, 'E6': j*(c*A1 + cp*A3)*(1 + j) - 1}
out = {}
G4 = 2*A3 - (1 - j - 2*c*A2); out['G4'] = find_lc(G4, {k: H[k] for k in ('hj', 'E4')}, V, 2); H['G4'] = G4
G5 = 2*A1 - (1 - j - 2*cp*A2); out['G5'] = find_lc(G5, {k: H[k] for k in ('hj', 'E5')}, V, 2); H['G5'] = G5
H2 = c*(j + A2*(1 + c - j*cp)) - 1; out['H2'] = find_lc(H2, {k: H[k] for k in ('hj', 'E2', 'G4', 'G5')}, V, 2); H['H2'] = H2
H3 = cp*(j + A2*(1 + cp - j*c)) - 1; out['H3'] = find_lc(H3, {k: H[k] for k in ('hj', 'E3', 'G4', 'G5')}, V, 2); H['H3'] = H3
H6 = j*(c + cp) - 2*j*(1 + j)*c*cp*A2 - 1; out['H6'] = find_lc(H6, {k: H[k] for k in ('hj', 'E6', 'G4', 'G5')}, V, 2); H['H6'] = H6
F1 = A2*(1 - c - cp) - j; out['F1'] = find_lc(F1, {k: H[k] for k in ('hj', 'E1', 'E4', 'E5')}, V, 2)
for k, v in out.items(): print(k, v)
# case cp = c
W = [j, c, A2]
G1c = A2*(1 - 2*c) - j
H2c = c*(j + A2*(1 + c - j*c)) - 1
H6c = 2*j*c - 2*j*(1 + j)*c**2*A2 - 1
for d in (2, 3, 4):
    r = find_lc(sp.Integer(1), {'G1c': G1c, 'H2c': H2c, 'H6c': H6c, 'hj': j*j + 1}, W, d)
    print('final deg', d, r)
    if r: break
