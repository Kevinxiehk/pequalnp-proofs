# EXACT FO2-joint test for D = dim X + 4 (Lagrangian case) [NOTES-stage2 R10-4], sympy over QQ.
# L level, X in L  =>  L in T_1(X) and L is totally isotropic for every q_m = D^2 perm(J+m), m in X; X lies in the radical of every q_m on T_1(X).
# If dim T_1(X)/X = 8 and dim L = dim X + 4, then L/X is Lagrangian for a nondegenerate Q1 in the span S of the q_m, hence invariant under
# every Q1^{-1} F, F in S. If these operators generate the full matrix algebra M_8, no such L exists.
# usage: r10_FO2J_exact.py NAME     NAME in D003A (cand_D003P_l1m1, A = C(1,-1,0,0), Case A), D04Pa (D04-PROP, alpha = (1,1,-1,-1), sg = 2)
import sys, itertools, sympy as sp
name=sys.argv[1]
z=sp.symbols('z1:6')
def mat(rows):
    M=sp.zeros(5,5)
    for (i,j),v in rows.items(): M[i,j]=v
    return M
if name=='D003A':
    Bs=[mat({(1,0):1,(2,0):-1}), mat({(3,0):1,(4,0):-1}), mat({(3,1):1,(3,2):-1}), mat({(4,3):1,(4,4):-1}), mat({(4,1):1,(4,2):1,(4,3):-1,(4,4):-1})]
elif name=='S2s':
    sg=sp.Rational(-3)
    Bs=[mat({(1,0):sg,(2,0):-1-sg,(4,0):1}), mat({(3,0):-4,(3,1):1,(3,2):1,(3,3):1,(3,4):1}), mat({(3,1):1,(3,2):-1}),
        mat({(4,3):1,(4,4):-1}), mat({(3,1):-1,(3,2):-1,(3,3):1,(3,4):1})]
elif name=='D04Pa':
    sg=sp.Rational(-3)
    Bs=[mat({(1,0):sg,(2,0):-1-sg,(4,0):1}), mat({(3,0):-4,(3,1):1,(3,2):1,(3,3):1,(3,4):1}), mat({(3,1):1,(3,2):1,(3,3):-1,(3,4):-1}),
        mat({(4,1):1,(4,2):-1}), mat({(4,3):1,(4,4):-1})]
m=sum((z[k]*Bs[k] for k in range(5)),sp.zeros(5,5)); U=sp.ones(5,5)+m
def permsym(M):
    n=M.shape[0]
    if n==0: return sp.Integer(1)
    return sp.expand(sum(sp.prod([M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n))))
def minor(M,rows,cols): return M.extract([r for r in range(M.shape[0]) if r not in rows],[c for c in range(M.shape[1]) if c not in cols])
C=[permsym(minor(U,[i],[j])) for i in range(5) for j in range(5)]
t=sp.symbols('t0:25')
expr=sp.expand(sum(t[k]*C[k] for k in range(25)))
eqs=sp.Poly(expr,*z).coeffs()
A=sp.Matrix([[sp.Poly(e,*t).coeff_monomial(t[k]) for k in range(25)] for e in eqs])
NS=A.nullspace()                                        # basis of T_1(X) (25-vectors)
T1=sp.Matrix.hstack(*NS).T
Xm=sp.Matrix([[Bs[k][i,j] for i in range(5) for j in range(5)] for k in range(5)])
print(name,': dim T_1(X) =',T1.rows,' rank X =',Xm.rank(),' rank [X;T_1] =',sp.Matrix.vstack(Xm,T1).rank(),flush=True)
# complement of X inside T_1: greedily pick T_1 basis vectors independent of X
comp=[]; cur=Xm
for r in range(T1.rows):
    cand=sp.Matrix.vstack(cur,T1.row(r))
    if cand.rank()>cur.rank(): comp.append(T1.row(r)); cur=cand
Qm=sp.Matrix.vstack(*comp); nq=Qm.rows; print('complement dim',nq,flush=True)
# Hessian of perm at U: H[(i,j),(k,l)] = perm_3(U without rows i,k, cols j,l)
H=sp.zeros(25,25)
for i in range(5):
    for k in range(i+1,5):
        for j in range(5):
            for l in range(5):
                if j==l: continue
                v=permsym(minor(U,[i,k],[j,l])); H[5*i+j,5*k+l]=v; H[5*k+l,5*i+j]=v
F=(Qm*H*Qm.T).applyfunc(sp.expand)
# coefficient matrices of F as a polynomial in z
monos=set()
for e in F:
    if e!=0: monos|=set(sp.Poly(e,*z).monoms())
monos=sorted(monos)
mats=[]
for mo in monos:
    M=F.applyfunc(lambda e: sp.Poly(e,*z).coeff_monomial(mo) if e!=0 else 0); mats.append(M)
# span basis
V=sp.Matrix([[M[a,b] for a in range(nq) for b in range(nq)] for M in mats]); rk=V.rank()
basis=[]; cur=None
for M in mats:
    row=sp.Matrix([[M[a,b] for a in range(nq) for b in range(nq)]])
    cand=row if cur is None else sp.Matrix.vstack(cur,row)
    if cand.rank()>(0 if cur is None else cur.rank()): basis.append(M); cur=cand
print('span of the forms q_m on T_1/X: dim',len(basis),flush=True)
# ---- export: common isotropic k-subspaces of the span (k = int(sys.argv[2]) if given else nq//2), all charts of Gr(k,nq), Singular over QQ
k=int(sys.argv[2]) if len(sys.argv)>2 else nq//2
out=open('/home/kevxhk/work/L-gct-210/stage2/r9/FO2J_charts_%s_sgm3_k%d.sing'%(name,k),'w')
w=lambda x: out.write(x+'\n')
vars_=['y%d_%d'%(a,b) for a in range(k) for b in range(nq-k)]
w('ring R=0,(%s),dp; option(redSB);'%','.join(vars_))
for idx,M in enumerate(basis):
    w('matrix F%d[%d][%d]=%s;'%(idx,nq,nq,','.join(str(M[a,b]) for a in range(nq) for b in range(nq))))
w('int nonunit=0; int nch=0; matrix Lm[%d][%d]; matrix P; ideal I; int a; int b;'%(k,nq))
for S in itertools.combinations(range(nq),k):
    rest=[c for c in range(nq) if c not in S]
    w('Lm=0;')
    for a in range(k):
        w('Lm[%d,%d]=1;'%(a+1,S[a]+1))
        for bi,c in enumerate(rest): w('Lm[%d,%d]=y%d_%d;'%(a+1,c+1,a,bi))
    w('I=0;')
    for idx in range(len(basis)):
        w('P=Lm*F%d*transpose(Lm); for(a=1;a<=%d;a++){for(b=a;b<=%d;b++){I=I+ideal(P[a,b]);}}'%(idx,k,k))
    w('I=std(I); nch++; if(reduce(1,I)!=0){nonunit++; "NONUNIT chart %s"; I;}'%(str(S)))
w('"RESULT FO2J charts %s k=%d: charts",nch,", non-unit charts",nonunit;'%(name,k))
w('quit;')
out.close(); print('written charts script, k =',k,flush=True)
