# EXACT counterexample to EL-SAT (NOTES-reg2 10.1): a saturated deletable-row space M_S = S (+) e_i (x) U_S, U_S = (C(S)+C1)^perp,
# with Omega(M_S) NOT inside A(U_S).  S = C Y0, Y0 in M_1 for the (2,2|2) member mu = (0,1,2,3) (row 1 deletable).  sympy, exact over Q.
import itertools, sympy as sp
def perm(M):
    n=M.shape[0]
    return sp.Add(*[sp.Mul(*[M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n))])
def fam22(m3,m4):
    S=1+m3+m4; B=[sp.zeros(4,5) for _ in range(6)]
    B[0][0,1:]=sp.Matrix([[m3-1,-m3,1,0]]); B[1][0,1:]=sp.Matrix([[m4-1,-m4,0,1]])
    B[2][1,:]=sp.Matrix([[4,-1,-1,-1,-1]]); B[3][1,:]=sp.Matrix([[-S,-S,5-S,5*m3-S,5*m4-S]])
    B[4][0,0]=1; B[4][2,0]=-1; B[5][2,0]=1; B[5][3,0]=-1
    return B
def T1_exact(B):
    ys=sp.symbols('y1:%d'%(len(B)+1)); A=sp.ones(5,5)
    for k,b in enumerate(B): A[:4,:]+=ys[k]*b
    rows={}
    for i in range(5):
        for j in range(5):
            m=A.copy(); m.row_del(i); m.col_del(j); P=sp.Poly(sp.expand(perm(m)),*ys)
            for mon,cf in P.terms(): rows.setdefault(mon,[0]*25); rows[mon][5*i+j]+=cf
    Am=sp.Matrix(list(rows.values())); N=Am.nullspace(); return Am,N
def AU(U):
    ann=sp.Matrix.vstack(*(U+[sp.ones(1,5)])).nullspace()     # a with <u,a> = 0, <1,a> = 0
    conds=[sp.Matrix([[a[j]*u[j] for j in range(5)]]) for a in ann for u in U]
    return sp.Matrix.vstack(*conds).nullspace() if conds else [sp.eye(5)[:,k] for k in range(5)]
B=fam22(2,3)
Mi=[B[0],B[1],B[4],B[5]]                     # the elements with row 1 = 0
Y0=Mi[0]+2*Mi[1]-Mi[2]+3*Mi[3]
y=sp.symbols('y'); D=[]
for j in range(5):
    m=sp.ones(4,5)+y*Y0; m.col_del(j); D.append(sp.Poly(sp.expand(perm(m))-24,y))
C=[sp.Matrix([[D[j].coeff_monomial(y**k) for j in range(5)]]) for k in range(1,5)]
Cm=sp.Matrix.vstack(*C); print('rank C(S) =',Cm.rank())
U=[u.T for u in sp.Matrix.vstack(Cm,sp.ones(1,5)).nullspace()]   # rows u with <c,u> = 0, <1,u> = 0
print('dim U =',len(U))
MS=[Y0]
for u in U:
    m=sp.zeros(4,5); m[1,:]=u; MS.append(m)
ys=sp.symbols('z1:%d'%(len(MS)+1)); A=sp.ones(4,5)
for k,b in enumerate(MS): A+=ys[k]*b
lev=sp.expand(sum(perm(A[:, [c for c in range(5) if c!=j]]) for j in range(5))-120); print('M_S level identity:',lev==0)
Am,N=T1_exact(MS); rho=sp.Matrix.hstack(*[n[20:,:] for n in N]); print('dim T_1 =',len(N),' dim Omega =',rho.rank())
Ab=AU(U); print('dim A(U) =',len(Ab))
Om=rho.T; Abm=sp.Matrix.hstack(*Ab).T
print('Omega inside A(U):',sp.Matrix.vstack(Abm,Om).rank()==Abm.rank())
