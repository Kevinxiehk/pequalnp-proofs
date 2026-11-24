import sympy as sp
al,be,ga,nu,x,y,z=sp.symbols('al be ga nu x y z')
# equations as lhs (=0)
E1 = al*nu + be*z + ga*y
E2 = al*z + be*nu + ga*x
E3 = al*y + be*x + ga*nu
E4 = 3*nu + 2*(x+y+z) - nu
A = sp.Matrix([[0,ga,be],[ga,0,al],[be,al,0],[2,2,2]])  # coefficients of x,y,z in E1..E4
rhs = sp.Matrix([al*nu, be*nu, ga*nu, 2*nu])
M = A.row_join(rhs)
# left null vector: cofactors along last column
C = [ (-1)**(i+3) * M.minor_submatrix(i,3).det() for i in range(4)]
comb = sp.expand(sum(c*e for c,e in zip(C,[E1,E2,E3,E4])))
print('C =', [sp.factor(c) for c in C])
print('comb =', sp.factor(comb))
target = (al+be-ga)*(al-be+ga)*(-al+be+ga)
print(sp.factor(comb/(nu*target)))
