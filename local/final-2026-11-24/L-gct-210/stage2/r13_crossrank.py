# Rank of the T_1 system of the cross-type family over the chart a4 = 1: gcd of determinants of random integer 12x12 compressions.
import random, sympy as sp
random.seed(5)
exec(open('/home/kevxhk/work/L-gct-210/stage2/r13_crossfam.py').read().split("R,piv=Am.rref")[0])
def rnd(r,c): return sp.Matrix(r,c,lambda i,j: random.randint(-3,3))
g=0
for _ in range(3):
    d=sp.factor((rnd(12,Am.rows)*Am*rnd(25,12)).det()); g=sp.gcd(g,d) if g!=0 else d
    print('compression det factor:',sp.factor(d),flush=True)
print('gcd:',sp.factor(g))
