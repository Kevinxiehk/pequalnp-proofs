import sympy as sp, sys
sys.argv=['x']; src=open('fam1111_mine.py').read().split("A=A.applyfunc(sp.expand)")[0]
exec(src)
from sympy.polys.matrices import DomainMatrix
A=A.applyfunc(sp.expand)
for av in (0,-2):
    print('a =',av,': dim T_1 =',25-A.subs(a,av).rank(),' dim M =',sp.Matrix([list(g) for g in G]).subs(a,av).rank())
w=(-1+sp.sqrt(-3))/2; K=sp.QQ.algebraic_field(sp.sqrt(-3))
Aw=A.subs(a,w).applyfunc(sp.expand); dm=DomainMatrix.from_Matrix(Aw).convert_to(K)
Gw=sp.Matrix([list(g) for g in G]).subs(a,w).applyfunc(sp.expand); dg=DomainMatrix.from_Matrix(Gw).convert_to(K)
print('a = omega: dim T_1 =',25-dm.rank(),' dim M =',dg.rank())
