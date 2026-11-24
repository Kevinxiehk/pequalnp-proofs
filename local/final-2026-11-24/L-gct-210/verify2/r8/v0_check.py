# verify2 r9: direct exact level check of reg2 11.4 V0 members (no helper), as a polynomial identity (sympy).
import sympy as sp, itertools
def member(s):
    u=sp.Matrix([1,s,-1-s,0,0])
    # U_0 = {w : w_3 = 0, sum w = 0, <w,u> = 0}
    A=sp.Matrix([[1,1,1,1,1],[0,0,0,1,0],list(u)]); U0=A.nullspace()
    rows=[]
    for w in U0: M=sp.zeros(4,5); M[0,:]=w.T; rows.append(M)
    M=sp.zeros(4,5); M[1,:]=u.T; rows.append(M)
    for v in ([0,1,-1,0],[0,0,1,-1]):
        M=sp.zeros(4,5); M[:,4]=sp.Matrix(v); rows.append(M)
    M=sp.zeros(4,5); M[:,3]=sp.Matrix([3,-1,-1,-1]); rows.append(M)
    return rows,U0
for s in (2,-5,3,sp.Rational(1,2),sp.Symbol('s')):
    B,U0=member(s); y=sp.symbols('y0:6')
    X=sum((y[k]*B[k] for k in range(6)),sp.zeros(4,5))
    A=sp.ones(5,5); A[0:4,:]=A[0:4,:]+X
    p=sp.expand(sp.Matrix(A).per()-120)
    print('s =',s,' U0 =',[list(w) for w in U0],'  perm(J+x)-120 =',sp.factor(p) if p!=0 else 0, flush=True)
