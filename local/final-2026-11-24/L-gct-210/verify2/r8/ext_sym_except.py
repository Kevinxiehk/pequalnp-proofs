# verify2 r9: exceptional sg for the symbolic D04-PROP extension test: (a) rank of the cofactor matrix < 11 (T' jumps), (b) rank [X;U] < 14.
# gcd of determinants of random integer projections (each det is in the ideal of maximal minors), then exact check at each root.
import random, json, sympy as sp
exec(open('/home/kevxhk/work/L-gct-210/verify2/r8/ext_T1_sym.py').read().split('K=sp.QQ.frac_field(sg)')[0])
M=sp.Matrix(rows)
D=json.load(open('/home/kevxhk/work/L-gct-210/verify2/r8/ext_T1_sym.json'))
XU=sp.Matrix([[sp.sympify(e) for e in v] for v in D['X']+D['U']])
random.seed(3)
def gdet(A,r,trials=4):
    g=0
    for _ in range(trials):
        R=sp.Matrix(r,A.rows,lambda i,j: random.randint(-3,3)); C=sp.Matrix(A.cols,r,lambda i,j: random.randint(-3,3))
        d=sp.expand((R*A*C).det(method='berkowitz')); g=sp.gcd(g,d)
    return sp.factor(g)
ga=gdet(M,11); gb=gdet(XU,14)
print('gcd for cofactor rank 11:',ga); print('gcd for [X;U] rank 14:',gb)
cands=set(sp.roots(sp.Poly(ga*gb,sg)).keys()) if sp.Poly(ga*gb,sg).degree()>0 else set()
for r in cands:
    print('candidate sg =',r,' rank cof =',M.subs(sg,r).rank(),' rank [X;U] =',XU.subs(sg,r).rank())
