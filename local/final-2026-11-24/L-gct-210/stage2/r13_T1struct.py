# Explicit T_1(X) for an F2col member (exact, sympy): print an RREF basis of T_1 modulo X to read off the structure.
import sys, itertools, sympy as sp
z=sp.symbols('z1:6')
def mat(rows):
    M=sp.zeros(5,5)
    for (i,j),v in rows.items(): M[i,j]=v
    return M
name=sys.argv[1]
if name=='K33':
    Bs=[mat({(1,0):1,(2,0):-1}), mat({(1,1):1,(2,1):1,(3,1):-2}), mat({(4,0):1,(4,1):2,(4,2):-3}), mat({(4,1):1,(4,2):1,(4,3):-2}), mat({(4,0):2,(4,2):1,(4,3):1,(4,4):-4})]
elif name=='crossA':  # P = 2-dim single column (column 0, rows 1,2,3 sum 0), Z = (0; 1^perp) in row 4
    Bs=[mat({(1,0):1,(2,0):-1}), mat({(2,0):1,(3,0):-1}), mat({(4,1):1,(4,2):-1}), mat({(4,2):1,(4,3):-1}), mat({(4,3):1,(4,4):-1})]
m=sum((z[k]*Bs[k] for k in range(5)),sp.zeros(5,5)); U=sp.ones(5,5)+m
def permsym(M):
    n=M.shape[0]; return sp.expand(sum(sp.prod([M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n))))
def minor(M,rows,cols): return M.extract([r for r in range(5) if r not in rows],[c for c in range(5) if c not in cols])
C=[permsym(minor(U,[i],[j])) for i in range(5) for j in range(5)]
t=sp.symbols('t0:25'); expr=sp.expand(sum(t[k]*C[k] for k in range(25)))
eqs=sp.Poly(expr,*z).coeffs()
A=sp.Matrix([[sp.Poly(e,*t).coeff_monomial(t[k]) for k in range(25)] for e in eqs])
R,piv=A.rref(); R=R[:len(piv),:]
print('T_1 defined by',len(piv),'independent linear equations (dim T_1 =',25-len(piv),'):')
names=['t%d%d'%(i,j) for i in range(5) for j in range(5)]
for r in range(R.rows):
    print('  ',' + '.join('%s*%s'%(R[r,c],names[c]) for c in range(25) if R[r,c]!=0),'= 0')
