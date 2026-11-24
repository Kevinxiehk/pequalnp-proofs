# Cross-type sub-family of F2col with general Z: X = (column 0, rows 1..3, sum 0) + e_4 (x) Z, Z = {z in 1^perp : z4 = -(a1 z1 + a2 z2 + a3 z3)}
# (chart a4 = 1 of the functional; WLOG by S_4 on columns 1..4). Exact T_1 over Q(a1,a2,a3), complement, forms; export a parametric chart script.
import sys, itertools, sympy as sp
a1,a2,a3=sp.symbols('a1 a2 a3'); A=[a1,a2,a3]; z=sp.symbols('z1:6')
def mat(rows):
    M=sp.zeros(5,5)
    for (i,j),v in rows.items(): M[i,j]=v
    return M
Bs=[mat({(1,0):1,(2,0):-1}), mat({(2,0):1,(3,0):-1})]
for k in range(3):
    zz=[0]*5; zz[k+1]=1; zz[4]=-A[k]; zz[0]=-(1-A[k])
    Bs.append(mat({(4,j):zz[j] for j in range(5)}))
m=sum((z[k]*Bs[k] for k in range(5)),sp.zeros(5,5)); U=sp.ones(5,5)+m
def permsym(M):
    n=M.shape[0]; return sp.expand(sum(sp.prod([M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n))))
def minor(M,rows,cols): return M.extract([r for r in range(5) if r not in rows],[c for c in range(5) if c not in cols])
C=[permsym(minor(U,[i],[j])) for i in range(5) for j in range(5)]
t=sp.symbols('t0:25'); expr=sp.expand(sum(t[k]*C[k] for k in range(25)))
eqs=sp.Poly(expr,*z).coeffs()
Am=sp.Matrix([[sp.Poly(e,*t).coeff_monomial(t[k]) for k in range(25)] for e in eqs])
R,piv=Am.rref(simplify=True); R=R[:len(piv),:]
print('generic: dim T_1 =',25-len(piv),flush=True)
names=['t%d%d'%(i,j) for i in range(5) for j in range(5)]
for r in range(R.rows):
    print('  ',' + '.join('(%s)*%s'%(sp.factor(R[r,c]),names[c]) for c in range(25) if R[r,c]!=0),'= 0',flush=True)
